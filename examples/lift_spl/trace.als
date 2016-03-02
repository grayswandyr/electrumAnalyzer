module trace[exactly elem]

private one sig Ord {
   First: set elem,
   Next: elem -> elem,
   Loop: elem -> elem
} {
   pred/totalOrder[elem,First,Next]
}

fact {
  Ord.Loop in last -> lone elem
}

fun first: one elem { Ord.First }

fun last: one elem { elem - ((Ord.Next).elem) }

fun next : elem->elem { Ord.Next + Ord.Loop }

fun prev : elem->elem { ~this/next }

fun past : elem->elem { ^(~this/next) }

fun future : elem -> elem { *this/next }

fun upto[s,s' : elem] : set elem {
	(s' in s.*(Ord.Next) or finite) implies s.future & ^(Ord.Next).s' else s.*(Ord.Next) + (^(Ord.Next).s' & last.(Ord.Loop).*(Ord.Next))
}

pred finite {
	no Loop
}

pred infinite {
	some Loop
}

check total {
	finite implies pred/totalOrder[elem,first,next]
}
