module examples/systems/marksweepgc

/*
 * Model of mark and sweep garbage collection.
 */

// a node in the heap
sig Node {}

sig HeapState {
  left, right : Node -> lone Node,
  marked : set Node,
  freeList : lone Node
}

pred clearMarks[hs, hs8 : HeapState] {
  // clear marked set
  no hs8.marked
  // left and right fields are unchanged
  hs8.left = hs.left
  hs8.right = hs.right
}

// simulate the recursion of the mark() function using transitive closure
fun reachable[hs: HeapState, n: Node] : set Node {
  n + n.^(hs.left + hs.right)
}

pred mark[hs: HeapState, from : Node, hs8: HeapState] {
  hs8.marked = hs.reachable[from]
  hs8.left = hs.left
  hs8.right = hs.right
}

// complete hack to simulate behavior of code to set freeList
pred setFreeList[hs, hs8: HeapState] {
  // especially hackish
  hs8.freeList.*(hs8.left) in (Node - hs.marked)
  all n: Node |
    (n !in hs.marked) => {
      no hs8.right[n]
      hs8.left[n] in (hs8.freeList.*(hs8.left))
      n in hs8.freeList.*(hs8.left)
    } else {
      hs8.left[n] = hs.left[n]
      hs8.right[n] = hs.right[n]
    }
  hs8.marked = hs.marked
}

pred GC[hs: HeapState, root : Node, hs8: HeapState] {
  some hs1, hs2: HeapState |
    clearMarks[hs, hs1] && mark[hs1, root, hs2] && setFreeList[hs2,hs8]
}

assert Soundness1 {
  all h, h8 : HeapState, root : Node |
   GC[h, root, h8] =>
      (all live : h.reachable[root] | {
        h8.left[live] = h.left[live]
        h8.right[live] = h.right[live]
      })
}

assert Soundness2 {
  all h, h8 : HeapState, root : Node |
    GC[h, root, h8] =>
      no h8.reachable[root] & h8.reachable[h8.freeList]
}

assert Completeness {
  all h, h8 : HeapState, root : Node |
    GC[h, root, h8] =>
      (Node - h8.reachable[root]) in h8.reachable[h8.freeList]
}

check Soundness1 for 3 expect 0
check Soundness2 for 3 expect 0
check Completeness for 3 expect 0
