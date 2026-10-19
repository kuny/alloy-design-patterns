module structural/component/Composite

abstract sig Component {
    parent: lone Component
}

sig Leaf extends Component {}

sig Composite extends Component {
    children: set Component
}

fact structural_invariants {
    // 親子の関係性は双方向で一致しなければならない
    all c: Component, p: Composite | c.parent = p <=> c in p.children

    // 循環参照の禁止
    all c: Component | c not in c.^parent

    // 孤立したノードを作らず、1つの木構造にする
    // （親がいないルート要素が「ちょうど1つ」存在し、すべての要素はルートの子孫である）
    one root: Component | {
        no root.parent
        Component in root.*children
    }
}

// インスタンス（具体的な木構造の例）を生成して確認するためのコマンド
pred show {
    // ルートは必ず Composite にする（Leaf 1つポツンを防止）
    some c: Composite | no c.parent
    
    // 木の中に、最低でも1つは Leaf が含まれるようにする
    some Leaf
}
run show for 5 Component

assert leaf_has_no_children {
    // どのLeafも、誰かの親（parentの関係先）にはなり得ない
    no l: Leaf | l in Component.parent
}
check leaf_has_no_children for 5

assert no_shared_children {
    // 異なる2つのCompositeが、同じ子を共有することはない
    all disj p1, p2: Composite | no (p1.children & p2.children)
}
check no_shared_children for 5

assert unique_root {
    lone c: Component | no c.parent
}
check unique_root for 5