module tour/addressBook1h ------- Page 14..16

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred show [b: Book] {
	#b.addr > 1
	#Name.(b.addr) > 1
}
run show for 3 but 1 Book

pred add [b, b8: Book, n: Name, a: Addr] {
	b8.addr = b.addr + n->a
}

pred del [b, b8: Book, n: Name] {
	b8.addr = b.addr - n->Addr
}

fun lookup [b: Book, n: Name] : set Addr {
	n.(b.addr)
}

pred showAdd [b, b8: Book, n: Name, a: Addr] {
	add [b, b8, n, a]
	#Name.(b8.addr) > 1
}
run showAdd for 3 but 2 Book

assert delUndoesAdd {
	all b, b8, b88: Book, n: Name, a: Addr |
		no n.(b.addr) and add [b, b8, n, a] and del [b8, b88, n]
		implies
		b.addr = b88.addr
}

assert addIdempotent {
	all b, b8, b88: Book, n: Name, a: Addr |
		add [b, b8, n, a] and add [b8, b88, n, a]
		implies
		b8.addr = b88.addr
}

assert addLocal {
	all b, b8: Book, n, n8: Name, a: Addr |
		add [b, b8, n, a] and n != n8
		implies
		lookup [b, n8] = lookup [b8, n8]
}

// This command should not find any counterexample.
check delUndoesAdd for 3

// This command should not find any counterexample.
check delUndoesAdd for 10 but 3 Book

// This command should not find any counterexample.
check addIdempotent for 3

// This command should not find any counterexample.
check addLocal for 3 but 2 Book
