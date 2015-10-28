one sig E {
	g : one E,
	f : disj (some { x, y : one E { one x, y : one E | one E } }.E),
}

run {}
