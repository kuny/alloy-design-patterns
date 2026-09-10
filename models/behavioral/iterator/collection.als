
module iterator/Collection

open iterator/element

sig Collection {
    items: seq Element
}

// Collection pred ==============

// Collection.contains(Element e)
pred contains [c: Collection, e: Element] {
    some i: c.items.inds | c.items[i] = e
}

// Collection.append(Element e)
pred append [c1, c2: Collection, e: Element] {
    // preconditions
    not contains[c1, e]

    // postconditions
    contains[c2, e]
}

// Collection.get(int index)
pred get[c: Collection, i: Int, e: Element] {
    // preconditions
    contains[c, e]

    // postconditions
    e = c.items[i]
}

// Collection.seek(Element e)
pred seek[c: Collection, e: Element, i: Int] {
    // preconditions
    contains[c, e]

    // postconditions
    e = c.items[i]
}


assert append_after_contains_true {
    all c1, c2: Collection, e: Element |
        append[c1, c2, e] => contains[c2, e]
}
check append_after_contains_true for 6