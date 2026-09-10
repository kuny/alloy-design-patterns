module iterator/iterator

//
// Iterator pattern
//
// In object-oriented programming, the iterator pattern is a design pattern 
// in which an iterator is used to traverse a container and access the container's elements. 
// The iterator pattern decouples algorithms from containers; in some cases, 
// algorithms are necessarily container-specific and thus cannot be decoupled.
//
// https://en.wikipedia.org/wiki/Iterator_pattern
//

sig Element {}

sig Collection {
    items: seq Element
}

sig Iterator {
    target: one Collection,
    index: one Int
}

// hasNext()
pred has_next [it: Iterator] {
    it.index >= 0 and it.index < #it.target.items
}

// next()
pred next [it1, it2: Iterator, elem: Element] {
    // preconditons
    has_next[it1]

    // postconditions
    elem = it1.target.items[it1.index]
    it2.target = it1.target
    it2.index = it1.index + 1
}

// contains(Element e)
pred contains [c: Collection, e: Element] {
    some i: c.items.inds | c.items[i] = e
}

// append(Element e)
pred append [c1, c2: Collection, e: Element] {
    // preconditions
    not contains[c1, e]

    // postconditions
    contains[c2, e]
}

assert next_returns_valid_element {
    all it1, it2: Iterator, e: Element |
        next[it1, it2, e] => {
            e in it1.target.items.elems
            it2.index = it1.index + 1
        }
}
check next_returns_valid_element for 6

assert append_after_contains_true {
    all c1, c2: Collection, e: Element |
        append[c1, c2, e] => contains[c2, e]
}
check append_after_contains_true for 6