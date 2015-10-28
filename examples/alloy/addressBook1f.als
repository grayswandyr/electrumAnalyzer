module tour/addressBook1f ----- Page 12

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred add [b, b8: Book, n: Name, a: Addr] {
	b8.addr = b.addr + n->a
}

pred showAdd [b, b8: Book, n: Name, a: Addr] {
	add [b, b8, n, a]
	#Name.(b8.addr) > 1
}

// This command generates an instance similar to Fig 2.5
run showAdd for 3 but 2 Book
