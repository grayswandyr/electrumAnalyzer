module appendixA/addressBook2

sig Addr, Name { }

sig Book {
	addr: Name -> (Name + Addr)
	}

pred inv [b: Book] {
	let addr2 = b.addr |
		all n: Name {
			n not in n.^addr2
			some addr2.n => some n.^addr2 & Addr
		}
	}

pred add [b, b8: Book, n: Name, t: Name+Addr] {
	b8.addr = b.addr + n->t
	}

pred del [b, b8: Book, n: Name, t: Name+Addr] {
	b8.addr = b.addr - n->t
	}

fun lookup [b: Book, n: Name] : set Addr {
	n.^(b.addr) & Addr
	}
