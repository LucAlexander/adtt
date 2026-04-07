const std = @import("std");
const Buffer = std.ArrayList;
const Map = std.StringHashMap;

const State = u8;
const Param = u8;
const Name = u8;

const Claim = union(enum){
	impl: struct {
		left: *Claim,
		right: *Claim
	},
	in: struct {
		left: *Claim,
		right: *Claim
	},
	not: *Claim,
	state: State,
	param: Param,
	named: struct {
		left: *Claim,
		right: *Claim,
		name: Name
	},

	pub fn eql(left: Claim, right: Claim) bool {
		if (std.meta.activeTag(left) == std.meta.activeTag(right)){
			return false;
		}
		switch (left){
			.impl => {
				return Claim.eql(left.impl.left.*, right.impl.left.*) and Claim.eql(left.impl.right.*, right.impl.right.*);
			},
			.in => {
				return Claim.eql(left.in.left.*, right.in.left.*) and Claim.eql(left.in.right.*, right.in.right.*);
			},
			.not => {
				return Claim.eql(left.not.*, right.not.*);
			},
			.state => {
				return left.state == right.state;
			},
			.param => {
				return left.param == right.param;
			},
			.named => {
				return Claim.eql(left.named.left.*, right.named.left.*) and Claim.eql(left.named.right.*, right.named.right.*) and left.named.name == right.named.name;
			}
		}
	}
};

const Arg = union(enum){
	state: State,
	param: Param
}

const Definition = struct {
	body: Buffer(Claim),
	claim: Claim,
	name: Name,
	
	pub fn init(name: Name, claim: Claim, body: Buffer(Claim)) Definition {
		std.debug.assert(claim == .impl);
		return Definition{
			.name = name,
			.claim = claim,
			.body = body
		};
	}

	pub fn contains(self: *Definition, claim: Claim, mind: *Mind) bool {
		for (self.body.items) |constraint| {
			if (constraint == .named){
				for (mind.definitions.items) |def| {
					if (def.name == constraint.named.name){
						if (constraint.contains(claim, mind)){
							return true;
						}
						break;
					}
				}
			}
			else{
				if (Claim.eql(constraint, claim)){
					return true;
				}
			}
		}
		return false;
	}

	pub fn copy(self: *Definition, mem: *const std.mem.Allocator) Definition {
		//TODO
	}

	pub fn eql(left: Definition, right: Definition) bool {
		if (left.name == right.name){
			return true;
		}
		if (Claim.eql(left.claim, right.claim) == false){
			return false;
		}
		if (left.body.items.len != right.body.items.len){
			return false;
		}
		for (left.body.items, right.body.items) |l, r| {
			if (Claim.eql(l, r) == false){
				return false;
			}
		}
		return true;
	}
};

const Mind = struct {
	definitions: Set(Definition),
	proofs: Set(Definition),
	mem: *const std.mem.Allocator,

	pub fn init(mem: *const std.mem.Allocator) Mind {
		return Mind{
			.mem = mem,
			.definitions = Set(Definition).init(mem)
			.proofs = Set(Definition).init(mem)
		};
	}

	pub fn prove(self: *Mind, def: *Definition, local_scope: *Set(Claim).init(self.mem.*), argmap: *std.AutoHashMap(Param, Claim)) bool {
		for (self.proofs.items) |proof| {
			local_scope.put(proof.claim);
		}
		local_scope.put(def.claim.impl.left);
		var i: u64 = 0;
		while (i < def.body.items.len){
			const constraint = &def.body.items[i];
			if (self.prove_target(def, argmap, constraint, &local_scope) == false){
				return false;
			}
			i += 1;
		}
		if (self.shows(def, argmap, def.claim, &local_scope) == false) {
			return false;
		}
	}
	//TODO at call: self.proofs.put(def);

	pub fn prove_target(self: *Mind, def: Definition, argmap: *std.AutoHashMap(Param, Claim), proof: *Claim, local_scope: *Set(Claim)) bool {
		switch (proof.*){
			.impl => {
				return self.shows(def, argmap, proof, local_scope);
			},
			.in => {
				if (self.get_definition(proof.in.right)) |definition| {
					var copy = definition.copy(self.mem);
					var newmap = std.AutoHashMap(Param, Claim).init(self.mem.*);
					var newscope = Set(Claim).init(self.mem);
					for (local_scope.data.items) |scope_item| {
						newscope.put(scope_item);
					}
					if (self.apply_argmap(&newmap, copy.claim, proof.in.right) == false) {
						return false;
					}
					if (self.prove(&copy, newscope, newmap) == false){
						return false;
					}
					return definition.contains(proof.in.left, self);
				}
				return false;
			},
			.not => {
				return !self.prove_target(def, argmap, proof.not, local_scope);
			},
			.state => {
				return self.shows(def, argmap, proof, local_scope);
			},
			.param => {
				if (argmap.get(proof.param)) |claim| {
					proof.* = claim;
					return self.prove_target(def, argmap, proof, local_scope);
				}
				return false;
			},
			.named => {
				for (self.definitions.items) |definition| {
					if (definition.name == self.named.name){
						var copy = definition.copy(self.mem);
						var newmap = std.AutoHashMap(Param, Claim).init(self.mem.*);
						var newscope = Set(Claim).init(self.mem);
						for (local_scope.data.items) |scope_item| {
							newscope.put(scope_item);
						}
						if (self.apply_argmap(&newmap, copy.claim, proof.in.right) == false){
							return false;
						}
						if (self.prove(&copy, newscope, newmap) == false){
							return false;
						}
						local_scope.put(copy.claim);
						return true;
					}
				}
				return false;
			}
		}
		return false;
	}

	pub fn shows(self: *Mind, def: Definition. argmap: *std.AutoHashMap(Param, Claim), claim: *Claim, local_scope: *Set(Claim)) bool {
		var target: ?Claim = null;
		if (claim == .impl){
			if (local_scope.contains(claim.impl.left) == false){
				return false;
			}
			if (local_scope.contains(claim.impl.right)){
				return true;
			}
			target = claim.impl.right;
		}
		else if (claim == .state){
			target = claim;
		}
		else{
			return false;
		}
		std.debug.assert(target != null);
		var old_len:u64 = 0;
		var len:u64 = local_scope.data.items.len;
		while (len != old_len){
			old_len = len;
			for (local_scope.data.items) |rule| {
				std.debug.assert(rule != .named);
				if (rule == .impl){
					if (local_scope.contains(rule.impl.left)){
						if (Claim.eql(target, rule.impl.right)){
							return true;
						}
						local_scope.put(rule.impl.right);
						break;
					}
				}
			}
			len = local_scope.data.items.len;
		}
		if (local_scope.contains(target)){
			return true;
		}
		return false;
	}

	pub fn apply_argmap(argmap: *std.AutoHashMap(Param, Claim), defclaim: Claim, claim: Claim) bool {
		if (std.meta.activeTag(defclaim) != std.meta.activeTag(claim)){
			if (defclaim == .param){
				argmap.put(defclaim.param, claim) catch unreachable;
				return true;
			}
		}
		if (claim == .param){
			return false;
		}
		switch (claim){
			.impl => {
				return apply_argmap(argmap, defclaim.impl.left, claim.impl.left) and apply_argmap(argmap, defclaim.impl.right, claim.impl.right);
			},
			.in => {
				return apply_argmap(argmap, defclaim.in.left, claim.in.left) and apply_argmap(argmap, defclaim.in.right, claim.in.right);
			},
			.not => {
				return apply_argmap(argmap, defclaim.not, claim.not);
			},
			.state => {
				return true;
			},
			.named => {
				if (defclaim.named.name != claim.named.name) {
					return false;
				}
				return apply_argmap(argmap, defclaim.named.left, claim.named.left) and apply_argmap(argmap, defclaim.named.right, claim.named.right);
			}
			else => {
				return false;
			}
		}
		return false;
	}

	pub fn get_definition(self: *Mind, claim: Claim) ?Definition {
		if (claim != .named){
			return null;
		}
		for (self.definitions.items) |def| {
			if (def.name == claim.named.name){
				return def;
			}
		}
		return null;
	}
};

pub fn Set(comptime T: type) type {
	return struct {
		const Self = @This();
		data: Buffer(T),

		pub fn init(mem: *const std.mem.Allocator) Self {
			return Self{
				.data = Buffer(T).init(mem.*)
			};
		}

		pub fn put(self: *Self, elem: T) void {
			for (self.data.items) |item| {
				if (T.eql(elem, item)){
					return;
				}
			}
			self.data.append(elem)
				catch unreachable;
		}

		pub fn contains(self: *Self, elem: T) bool {
			for (self.data.items) |item| {
				if (T.eql(item, elem)){
					return true;
				}
			}
			return false;
		}

		pub fn remove(self: *Self, elem: T) bool {
			for (self.data.items, 0..) |item, i| {
				if (T.eql(item, elem)){
					_ = self.data.swapRemove(i);
					return true;
				}
			}
			return false;
		}

		pub fn eql(a: Self, b: Self) bool {
			if (a.data.items.len != b.data.items.len){
				return false;
			}
			outer: for (a.data.items) |i| {
				for (b.data.items) |k| {
					if (T.eql(i, k)){
						continue :outer;
					}
				}
				return false;
			}
			return true;
		}
	};
}

pub fn SetPrimitive(comptime T: type) type {
	return struct {
		const Self = @This();
		data: Buffer(T),

		pub fn init(mem: *const std.mem.Allocator) Self {
			return Self{
				.data = Buffer(T).init(mem.*)
			};
		}

		pub fn put(self: *Self, elem: T) void {
			for (self.data.items) |item| {
				if (elem == item){
					return;
				}
			}
			self.data.append(elem)
				catch unreachable;
		}

		pub fn contains(self: *Self, elem: T) bool {
			for (self.data.items) |item| {
				if (item==elem){
					return true;
				}
			}
			return false;
		}

		pub fn remove(self: *Self, elem: T) bool {
			for (self.data.items, 0..) |item, i| {
				if (item==elem){
					_ = self.data.swapRemove(i);
					return true;
				}
			}
			return false;
		}

		pub fn eql(a: Self, b: Self) bool {
			if (a.data.items.len != b.data.items.len){
				return false;
			}
			outer: for (a.data.items) |i| {
				for (b.data.items) |k| {
					if (i==k){
						continue :outer;
					}
				}
				return false;
			}
			return true;
		}
	};
}

pub fn main() !void {
	const heap = std.heap.page_allocator;
	const main_buffer = heap.alloc(u8, 0x10000) catch unreachable;
	const temp_buffer = heap.alloc(u8, 0x10000) catch unreachable;
	var main_mem_fixed = std.heap.FixedBufferAllocator.init(main_buffer);
	var temp_mem_fixed = std.heap.FixedBufferAllocator.init(temp_buffer);
	var main_mem = main_mem_fixed.allocator();
	var temp_mem = temp_mem_fixed.allocator();

}
