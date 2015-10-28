module appendixA/addressBook1

sig Addr { }

abstract sig Name {
	address: set Addr+Name
	}

sig Alias, Group extends Name { }

fact {
	// the invariants should go here
	}

pred show {
	// simulation constraints should go here
	}

run show for 3
