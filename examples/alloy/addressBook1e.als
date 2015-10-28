module tour/addressBook1e ----- Page 11

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred add [b, b8: Book, n: Name, a: Addr] {
	b8.addr = b.addr + n->a
}

// This command generates an instance similar to Fig 2.4
run add for 3 but 2 Book
