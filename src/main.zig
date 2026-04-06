const std = @import("std");
const Buffer = std.ArrayList;
const Map = std.StringHashMap;

const State = u8;
const Param = u8;
const Name = u8;

const Claim = union(enum){
	impl: struct {
		left: *Proof,
		right: *Proof
	},
	in: struct {
		left: *Proof,
		right: *Proof
	},
	not: *Proof,
	state: State,
	param: Param,
	named: Name,

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
				return left.named == right.named;
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
	name: Name,
	leftarg: Arg,
	rightarg: Arg,
	
	pub fn eql(left: Definition, right: Definition) bool {
		if (left.name == right.name){
			return true;
		}
		if ((left.leftarg == .state and right.leftarg != .state) or
			(left.leftarg == .param and right.leftarg != .param)) {
			return false;
		}
		if ((left.rightarg == .state and right.rightarg != .state) or
			(left.rightarg == .param and right.rightarg != .param)) {
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

	pub fn init(mem: *const std.mem.Allocator) Mind {
		return Mind{
			.definitions = Set(Definition).init(mem),
			.proofs = Set(Definition).init(mem)
		};
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
