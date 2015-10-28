module examples/case_studies/sync

/*
 * Model of a generic file synchronizer.
 *
 * Adapted from:
 *   Reference: S. Balasubramaniam and Benjamin C. Pierce,
 *   "What is a File Synchronizer", Indiana University CSCI
 *   Technical Report #507, April 22, 1998
 *
 * For a detailed description, see:
 *   http://sdg.lcs.mit.edu/pubs/theses/tnolte_masters.pdf
 *
 * author: Tina Nolte
 */

private open util/graph[Name] as graph

// The Name atom represents the hierarchy of all name sequences
// used in the model. A Name atom represents the name, and the path
// in the sequence of names to the root excluding the RootName.
sig Name {
  children: set Name
}

fact { graph/tree[children] }

one sig RootName extends Name { }

fact { Name in RootName.*children }

// We assume that the empty path always

sig FileContents { }
one sig Dir extends FileContents { }

pred IsValidFS[fs: Name -> lone FileContents] {
   all n: Name - RootName | {
      // files don8t have children
      n.fs != Dir => no (n.^children).fs
      // if a path maps to something non-nil, all prefixes do also
      some n.fs => some (n.~children).fs
   }
   // the root of a file system must be a directory
   RootName.fs = Dir
}

pred IsValidDirty[dirty: set Name] {
  all n: dirty | n.~children in dirty
  RootName in dirty => some dirty - RootName
}

pred DirtiesValid[A, B: Name -> lone FileContents, Adirty, Bdirty: set Name] {
  some O: Name -> lone FileContents | {
    IsValidFS[O]
    { n: Name | n.O != n.A } in Adirty
    { n: Name | n.O != n.B } in Bdirty
  }
}

fun RestrictFS[fs: Name -> lone FileContents, p: Name]: Name -> lone FileContents {
   fs & (p.*children -> FileContents)
}

fun RestrictFSComplement[fs: Name -> lone FileContents, p: Name]: Name -> lone FileContents {
   fs & ((Name - p.*children) -> FileContents)
}

// The following function test whether a particular synchronizer
// operation satisfies the "reasonableness" conditions.
// The arguments are:
// O - the original filesystem.
// A,B - separately modified copies
// Adirty, Bdirty - sets of paths modified in A and B, respectively, from O.
//
// A8,B8 - results of synchronizer operation
pred SyncSpec[A, B, A8, B8: Name -> lone FileContents, Adirty, Bdirty: set Name] {
  {
     IsValidFS[A]
     IsValidFS[B]
     IsValidDirty[Adirty]
     IsValidDirty[Bdirty]
   } => {
    {
     all p: Name | IsRelevantPath[p, A, B] => {
        SyncSpecForPath[p, A, B, A8, B8, Adirty, Bdirty]
     }
    }
    IsValidFS[A8]
    IsValidFS[B8]
   }
}

pred SyncSpecForPath[p: Name, A, B, A8, B8: Name -> lone FileContents, Adirty, Bdirty: set Name] {
      (p.A = p.B  =>  (p.A8 = p.A && p.B8 = p.B))
      (p !in Adirty => (RestrictFS[A8, p] = RestrictFS[B, p] && RestrictFS[B8, p] = RestrictFS[B, p]))
      (p !in Bdirty => (RestrictFS[B8, p] = RestrictFS[A, p] && RestrictFS[A8, p] = RestrictFS[A, p]))
      ((p in Adirty && p in Bdirty && p.A != p.B) => (RestrictFS[A8,p] = RestrictFS[A,p] && RestrictFS[B8,p] = RestrictFS[B,p]))
}

pred IsRelevantPath[p: Name, A, B: Name -> lone FileContents] {
   p = RootName || {
     (p.~children).A = Dir
     (p.~children).B = Dir
   }
}

pred SyncSpecExample[A, B, A8, B8: Name -> lone FileContents, Adirty, Bdirty: set Name] {
   IsValidFS[A]
   IsValidFS[B]
   IsValidDirty[Adirty]
   IsValidDirty[Bdirty]
   SyncSpec[A, B, A8, B8, Adirty, Bdirty]
   A != A8
}

//run SyncSpecExample for 3

pred SyncSpecNotUnique  {
  some A, B, A18, B18, A28, B28: Name -> lone FileContents, Adirty, Bdirty: set Name | {
    IsValidFS[A] && IsValidFS[B]
    IsValidDirty[Adirty] && IsValidDirty[Bdirty]
    //DirtiesValid(A, B, Adirty, Bdirty)
    (A18 != A28  || B18 != B28)
    SyncSpec[A, B, A18, B18, Adirty, Bdirty]
    SyncSpec[A, B, A28, B28, Adirty, Bdirty]
  }
}

run SyncSpecNotUnique for 5 expect 0
