const std = @import("std");
const Buffer = std.ArrayList;
const Map = std.StringHashMap;

const TOKEN = u64;
const OPEN_EXPR = '(';
const CLOSE_EXPR = ')';
const OPEN_PROOF = '{';
const CLOSE_PROOF = '}';
const END_EXPR = ';';
const SHOWS = 0;
const CONS = 1;
const FORALL = 2;
const IN = 3;
const IDENTIFIER = 2;

const Token = struct {
	tag: TOKEN,
	text: []const u8
};

const Theorem = struct {
	name: Token,
	arg: Token,
	body: Expr 
};

const Expr = union(enum){
	proof: Buffer(Expr),
	shows: struct{
		left: *Expr,
		right: *Expr 
	},
	cons: struct {
		left: *Expr,
		right: *Expr
	},
	call: struct {
		name: Token,
		arg: *Expr
	},
	arg: Token,
	forall: struct {
		arg: Token,
		container: *Expr,
		body: *Expr
	}
};

pub fn tokenize(mem: *const std.mem.Allocator, text: []const u8) Buffer(Token) {
	//TODO
}

pub fn parse(mem: *const std.mem.Allocator, tokens: []Token) Buffer(Theorem) {
	//TODO
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
