module tour/addressBook1g ----- Page 14

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred add [b, b8: Book, n: Name, a: Addr] {
	b8.addr = b.addr + n->a
}

pred del [b, b8: Book, n: Name] {
	b8.addr = b.addr - n->Addr
}

fun lookup [b: Book, n1: Name] : set Addr {
	n1.(b.addr)
}

assert delUndoesAdd {
	all b, b8, b88: Book, n2: Name, a: Addr |
		add [b, b8, n2, a] and del [b8, b88, n2]
		implies
		b.addr = b88.addr
}

// This command generates an instance similar to Fig 2.6
check delUndoesAdd for 3
