module tour/addressBook2e --- this is the final model in Fig 2.14

abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends Name { }

sig Book {
	names: set Name,
	addr: names->some Target
} {
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
}

pred add [b, b8: Book, n: Name, t: Target] { b8.addr = b.addr + n->t }
pred del [b, b8: Book, n: Name, t: Target] { b8.addr = b.addr - n->t }
fun lookup [b: Book, n: Name] : set Addr { n.^(b.addr) & Addr }

assert delUndoesAdd {
	all b, b8, b88: Book, n: Name, t: Target |
		no n.(b.addr) and add [b, b8, n, t] and del [b8, b88, n, t]
		implies
		b.addr = b88.addr
}

// This should not find any counterexample.
check delUndoesAdd for 3

assert addIdempotent {
	all b, b8, b88: Book, n: Name, t: Target |
		add [b, b8, n, t] and add [b8, b88, n, t]
		implies
		b8.addr = b88.addr
}

// This should not find any counterexample.
check addIdempotent for 3

assert addLocal {
	all b, b8: Book, n, n8: Name, t: Target |
		add [b, b8, n, t] and n != n8
		implies
		lookup [b, n8] = lookup [b8, n8]
}

// This shows a counterexample similar to Fig 2.13
check addLocal for 3 but 2 Book

assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
}

// This shows a counterexample similar to Fig 2.12
check lookupYields for 4 but 1 Book
