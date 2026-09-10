module behavioral/iterator/iterator

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

open behavioral/iterator/element
open behavioral/iterator/Collection[Element]

sig Iterator {
    target: one Collection,
    index: one Int
}

// Iterator.hasNext()
pred has_next [it: Iterator] {
    it.index >= 0 and it.index < #it.target.items
}

// Iterator.next()
pred next [it1, it2: Iterator, elem: Element] {
    // preconditons
    has_next[it1]

    // postconditions
    elem = it1.target.items[it1.index]
    it2.target = it1.target
    it2.index = it1.index + 1
}


assert next_returns_valid_element {
    all it1, it2: Iterator, e: Element |
        next[it1, it2, e] => {
            e in it1.target.items.elems
            it2.index = it1.index + 1
        }
}
check next_returns_valid_element for 6