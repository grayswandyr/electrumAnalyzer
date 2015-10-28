module chapter6/mediaAssets

sig ApplicationState {
	catalogs: set Catalog,
	catalogState: catalogs -> one CatalogState,
	currentCatalog: catalogs,
	buffer: set Asset
	}

sig Catalog, Asset {}

sig CatalogState {
	assets: set Asset,
	disj hidden, showing: set assets,
	selection: set assets + Undefined
	} {
	hidden+showing = assets
	}

one sig Undefined {}

pred catalogInv [cs: CatalogState] {
	cs.selection = Undefined or (some cs.selection and cs.selection in cs.showing)
	}

pred appInv [xs: ApplicationState] {
	all cs: xs.catalogs | catalogInv [cs.(xs.catalogState)]
	}

pred showSelected [cs, cs8: CatalogState] {
	cs.selection != Undefined
	cs8.showing = cs.selection
	cs8.selection = cs.selection
	cs8.assets = cs.assets
	}

pred hideSelected [cs, cs8: CatalogState] {
	cs.selection != Undefined
	cs8.hidden = cs.hidden + cs.selection
	cs8.selection = Undefined
	cs8.assets = cs.assets
	}

pred cut [xs, xs8: ApplicationState] {
	let cs = xs.currentCatalog.(xs.catalogState), sel = cs.selection {
		sel != Undefined
		xs8.buffer = sel
		some cs8: CatalogState {
			cs8.assets = cs.assets - sel
			cs8.showing = cs.showing - sel
			cs8.selection = Undefined
			xs8.catalogState = xs.catalogState ++ xs.currentCatalog -> cs8
			}
		}
	xs8.catalogs = xs.catalogs
	xs8.currentCatalog = xs.currentCatalog
	}

pred paste [xs, xs8: ApplicationState] {
	let cs = xs.currentCatalog.(xs.catalogState), buf = xs.buffer {
		xs8.buffer = buf
		some cs8: CatalogState {
			cs8.assets = cs.assets + buf
			cs8.showing = cs.showing + (buf - cs.assets)
			cs8.selection = buf - cs.assets
			xs8.catalogState = xs.catalogState ++ xs.currentCatalog -> cs8
			}
		}
	xs8.catalogs = xs.catalogs
	xs8.currentCatalog = xs.currentCatalog
	}

assert HidePreservesInv {
	all cs, cs8: CatalogState |
		catalogInv [cs] and hideSelected [cs, cs8] => catalogInv [cs8]
	}

// This check should not find any counterexample
check HidePreservesInv

pred sameApplicationState [xs, xs8: ApplicationState] {
	xs8.catalogs = xs.catalogs
	all c: xs.catalogs | sameCatalogState [c.(xs.catalogState), c.(xs8.catalogState)]
	xs8.currentCatalog = xs.currentCatalog
	xs8.buffer = xs.buffer
	}

pred sameCatalogState [cs, cs8: CatalogState] {
	cs8.assets = cs.assets
	cs8.showing = cs.showing
	cs8.selection = cs.selection
	}

assert CutPaste {
	all xs, xs8, xs9: ApplicationState |
		(appInv [xs] and cut [xs, xs8] and paste [xs8, xs9]) => sameApplicationState [xs, xs9] 
	}

// This check should find a counterexample
check CutPaste

assert PasteCut {
	all xs, xs8, xs9: ApplicationState |
		(appInv [xs] and paste [xs, xs8] and cut [xs8, xs9]) => sameApplicationState [xs, xs9] 
	}

// This check should find a counterexample
check PasteCut

assert PasteNotAffectHidden {
	all xs, xs8: ApplicationState |
		(appInv [xs] and paste [xs, xs8]) => 
			let c = xs.currentCatalog | (c.(xs8.catalogState)).hidden = (c.(xs.catalogState)).hidden
	}

// This check should not find any counterexample
check PasteNotAffectHidden
