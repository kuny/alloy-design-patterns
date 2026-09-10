module iterator/iterator

//
// 
//

sig Element {}

sig Collection {
    items: seq Element,
    var index: Int
}

pred has_next [c1: Collection] {
    c1.index in c1.items.inds
}

pred next [c1, c2: Collection, result: Element] {
    has_next[c1]
    result = c1.index.(c1.items)

    c2.index = add[c1.index, 1]
    c2.items = c1.items
}


run {} for 3 Element, 1 Collection
