module chapter6/memory/abstractMemory [Addr, Data] ----- the model from page 217

sig Memory {
	data: Addr -> lone Data
	}

pred init [m: Memory] {
	no m.data
	}

pred write [m, m8: Memory, a: Addr, d: Data] {
	m8.data = m.data ++ a -> d
	}

pred read [m: Memory, a: Addr, d: Data] {
	let d8 = m.data [a] | some d8 implies d = d8
	}

fact Canonicalize {
	no disj m, m8: Memory | m.data = m8.data
	}

// This command should not find any counterexample
WriteRead: check {
	all m, m8: Memory, a: Addr, d1, d2: Data |
		write [m, m8, a, d1] and read [m8, a, d2] => d1 = d2
	}

// This command should not find any counterexample
WriteIdempotent: check {
	all m, m8, m9: Memory, a: Addr, d: Data |
		write [m, m8, a, d] and write [m8, m9, a, d] => m8 = m9
	}
