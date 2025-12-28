import VersoManual
import TPiLZh.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiLZh

set_option linter.typography.dashes false

#doc (Manual) "量词与相等" =>
%%%
tag := "quantifiers-and-equality"
file := "QuantifiersEquality"
%%%
-- Quantifiers and Equality

```setup
variable {α : Type u} (p : α → Prop) (x y t : α) (r : α → α → Prop) {β : α → Type v}
```

-- The last chapter introduced you to methods that construct proofs of
-- statements involving the propositional connectives. In this chapter,
-- we extend the repertoire of logical constructions to include the
-- universal and existential quantifiers, and the equality relation.

上一章介绍了构造包含命题连接词的证明方法。在本章中，
我们扩展逻辑结构，包括全称量词和存在量词，以及相等关系。

-- # The Universal Quantifier
# 全称量词
%%%
tag := "the-universal-quantifier"
%%%

-- Notice that if {lean}`α` is any type, we can represent a unary predicate
-- {lean}`p` on {lean}`α` as an object of type {lean}`α → Prop`. In that case, given
-- {lean}`x : α`, {lean}`p x` denotes the assertion that {lean}`p` holds of
-- {lean}`x`. Similarly, an object {lean}`r : α → α → Prop` denotes a binary
-- relation on {lean}`α`: given {lean}`x y : α`, {lean}`r x y` denotes the assertion
-- that {lean}`x` is related to {lean}`y`.

如果 {lean}`α` 是任何类型，我们可以将 {lean}`α` 上的一元谓词 {lean}`p` 作为 {lean}`α → Prop` 类型的对象。在这种情况下，给定 {lean}`x : α`， {lean}`p x` 表示断言 {lean}`p` 在 {lean}`x` 上成立。类似地，一个对象 {lean}`r : α → α → Prop` 表示 {lean}`α` 上的二元关系：给定 {lean}`x y : α`，{lean}`r x y` 表示断言 {lean}`x` 与 {lean}`y` 相关。

-- The universal quantifier, {lean}`∀ x : α, p x` is supposed to denote the
-- assertion that “for every {lean}`x : α`, {lean}`p x`” holds. As with the
-- propositional connectives, in systems of natural deduction, “forall”
-- is governed by an introduction and elimination rule. Informally, the
-- introduction rule states:

全称量词 {lean}`∀ x : α, p x` 表示，对于每一个 {lean}`x : α`，{lean}`p x` 成立。与命题连接词一样，在自然演绎系统中，「forall」有引入和消去规则。非正式地，引入规则是：

-- > Given a proof of {lean}`p x`, in a context where {lean}`x : α` is arbitrary, we obtain a proof {lean}`∀ x : α, p x`.

> 在 {lean}`x : α` 是任意的情况下，给定 {lean}`p x` 的证明，就可以得到 {lean}`∀ x : α, p x` 的证明。

-- The elimination rule states:

消去规则是：

-- > Given a proof {lean}`∀ x : α, p x` and any term {lean}`t : α`, we obtain a proof of {lean}`p t`.

> 给定 {lean}`∀ x : α, p x` 的证明和任何项 {lean}`t : α`，就可以得到 {lean}`p t` 的证明。

-- As was the case for implication, the propositions-as-types
-- interpretation now comes into play. Remember the introduction and
-- elimination rules for dependent arrow types:

与蕴含的情况一样，命题即类型。回想依值箭头类型的引入规则：

```setup
variable {α : Type u} (p : α → Prop) (x y : α) (r : α → α → Prop) {β : α → Type v} {t : {x : α} → β x}
```
-- > Given a term {lean}`t` of type {lean}`β x`, in a context where {lean}`x : α` is arbitrary, we have {lean}`(fun x : α => t) : (x : α) → β x`.

> 在 {lean}`x : α` 是任意的情况下，给定类型为 {lean}`β x` 的项 {lean}`t`，就可以得到 {lean}`(fun x : α => t) : (x : α) → β x`。

```setup
variable {α : Type u} (p : α → Prop) (x y : α) (r : α → α → Prop) {β : α → Type v} {t : α} {s : (x : α) → β x}
```

-- The elimination rule states:

消去规则：

-- > Given a term {lean}`s : (x : α) → β x` and any term {lean}`t : α`, we have {lean}`s t : β t`.

> 给定项 {lean}`s : (x : α) → β x` 和任何项 {lean}`t : α`，就可以得到 {lean}`s t : β t`。

-- In the case where {lean}`p x` has type {lean}`Prop`, if we replace
-- {lean}`(x : α) → β x` with {lean}`∀ x : α, p x`, we can read these as the correct rules
-- for building proofs involving the universal quantifier.

在 {lean}`p x` 具有 {lean}`Prop` 类型的情况下，如果我们用 {lean}`∀ x : α, p x` 替换 {lean}`(x : α) → β x`，就得到构建涉及全称量词的证明的规则。

:::setup
```
variable {α : Type u} {β : Type v} {p : {x : α} → Prop} (q : Prop)
```
-- The Calculus of Constructions therefore identifies dependent arrow
-- types with forall-expressions in this way. If {lean}`p` is any expression,
-- {lean}`∀ x : α, p` is nothing more than alternative notation for
-- {lean}`(x : α) → p`, with the idea that the former is more natural than the latter
-- in cases where {lean}`p` is a proposition. Typically, the expression {lean}`p`
-- will depend on {leanRef}`x : α`. Recall that, in the case of ordinary
-- function spaces, we could interpret {lean}`α → β` as the special case of
-- {lean}`(x : α) → β` in which {lean}`β` does not depend on {leanRef}`x`. Similarly, we
-- can think of an implication {lean}`p → q` between propositions as the
-- special case of {lean}`∀ x : p, q` in which the expression {lean}`q` does not
-- depend on {leanRef}`x`.

因此，构造演算用全称表达式来识别依值箭头类型。如果 {lean}`p` 是任何表达式，{lean}`∀ x : α, p` 不过是 {lean}`(x : α) → p` 的替代符号，在 {lean}`p` 是命题的情况下，前者比后者更自然。通常，表达式 {lean}`p` 取决于 {leanRef}`x : α`。回想一下，在普通函数空间中，我们可以将 {lean}`α → β` 解释为 {lean}`(x : α) → β` 的特殊情况，其中 {lean}`β` 不依赖于 {leanRef}`x`。类似地，我们可以把命题之间的蕴涵 {lean}`p → q` 看作是 {lean}`∀ x : p, q` 的特殊情况，其中 {lean}`q` 不依赖于 {leanRef}`x`。
:::

-- Here is an example of how the {tech}[propositions-as-types] correspondence gets put into practice.

下面是一个例子，说明了如何运用 {tech}[命题即类型] 对应规则。

```lean
example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
```

-- As a notational convention, we give the universal quantifier the
-- widest scope possible, so parentheses are needed to limit the
-- quantifier over {leanRef}`x` to the hypothesis in the example above. The
-- canonical way to prove {lean}`∀ y : α, p y` is to take an arbitrary {leanRef}`y`,
-- and prove {leanRef}`p y`. This is the introduction rule. Now, given that
-- {leanRef}`h` has type {leanRef}`∀ x : α, p x ∧ q x`, the expression {leanRef}`h y` has type
-- {leanRef}`p`{lit}` `{leanRef}`y`{lit}`  ∧  `{leanRef}`q`{lit}` `{leanRef}`y`. This is the elimination rule. Taking the left conjunct
-- gives the desired conclusion, {leanRef}`p y`.

作为记法约定，我们给全称量词尽可能大的作用域，因此在上面的例子中需要括号来将 {leanRef}`x` 的量词限制在假设中。证明 {lean}`∀ y : α, p y` 的规范方法是取一个任意的 {leanRef}`y` 并证明 {leanRef}`p y`。这就是引入规则。现在，给定 {leanRef}`h` 的类型为 {leanRef}`∀ x : α, p x ∧ q x`，表达式 {leanRef}`h y` 的类型为 {leanRef}`p`{lit}` `{leanRef}`y`{lit}`  ∧  `{leanRef}`q`{lit}` `{leanRef}`y`。这就是消去规则。取左结合项得到了所需的结论 {leanRef}`p y`。

:::setup
```
variable {x z : α}
```

-- Remember that expressions which differ up to renaming of bound
-- variables are considered to be equivalent. So, for example, we could
-- have used the same variable, {lean}`x`, in both the hypothesis and
-- conclusion, and instantiated it by a different variable, {lean}`z`, in the
-- proof:

记住，在重命名绑定变量后相同的表达式被认为是等价的。例如，我们可以在假设和结论中使用相同的变量 {lean}`x`，并在证明中用不同的变量 {lean}`z` 来实例化它：
:::

```lean
example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```

-- As another example, here is how we can express the fact that a relation, {lean}`r`, is transitive:

作为另一个例子，下面是我们如何表达一个关系 {lean}`r` 是传递的：

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- trans_r : ∀ (x y z : α), r x y → r y z → r x z

#check trans_r a b c -- trans_r a b c : r a b → r b c → r a c

#check trans_r a b c hab -- trans_r a b c hab : r b c → r a c

#check trans_r a b c hab hbc -- trans_r a b c hab hbc : r a c
```

-- Think about what is going on here. When we instantiate {leanRef}`trans_r` at
-- the values {leanRef}`a b c`, we end up with a proof of {leanRef}`r`{lit}` `{leanRef}`a b`{lit}`  →  `{leanRef}`r`{lit}` `{leanRef}`b c`{lit}`  →  `{leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c`.
-- Applying this to the “hypothesis” {leanRef}`hab : r a b`, we get a proof
-- of the implication {leanRef}`r`{lit}` `{leanRef}`b c`{lit}`  →  `{leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c`. Finally, applying it to the
-- hypothesis {leanRef}`hbc` yields a proof of the conclusion {leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c`.

思考一下这里发生了什么。当我们用值 {leanRef}`a b c` 实例化 {leanRef}`trans_r` 时，我们最终得到了 {leanRef}`r`{lit}` `{leanRef}`a b`{lit}`  →  `{leanRef}`r`{lit}` `{leanRef}`b c`{lit}`  →  `{leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c` 的证明。将其应用于「假设」{leanRef}`hab : r a b`，我们得到了蕴涵式 {leanRef}`r`{lit}` `{leanRef}`b c`{lit}`  →  `{leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c` 的证明。最后，将其应用于假设 {leanRef}`hbc` 得到了结论 {leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c` 的证明。

-- In situations like this, it can be tedious to supply the arguments
-- {leanRef}`a b c`, when they can be inferred from {leanRef}`hab hbc`. For that reason, it
-- is common to make these arguments implicit:

在这种情况下，当可以从 {leanRef}`hab hbc` 推断出参数 {leanRef}`a b c` 时，提供这些参数可能会很繁琐。因此，通常将这些参数设为隐式：

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r

#check trans_r hab

#check trans_r hab hbc
```

-- The advantage is that we can simply write {leanRef}`trans_r hab hbc` as a
-- proof of {leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c`. A disadvantage is that Lean does not have enough
-- information to infer the types of the arguments in the expressions
-- {leanRef}`trans_r` and {leanRef}`trans_r hab`. The output of the first {kw}`#check`
-- command is {lit}`r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3`, indicating
-- that the implicit arguments are unspecified in this case.

这样做的好处是我们可以简单地将 {leanRef}`trans_r hab hbc` 写成 {leanRef}`r`{lit}` `{leanRef}`a`{lit}` `{leanRef}`c` 的证明。缺点是 Lean 没有足够的信息来推断表达式 {leanRef}`trans_r` 和 {leanRef}`trans_r hab` 中参数的类型。第一个 {kw}`#check` 命令的输出是 {lit}`r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3`，表示在这种情况下隐式参数是未指定的。

-- Here is an example of how we can carry out elementary reasoning with an equivalence relation:

下面是一个我们如何使用等价关系进行基本推理的例子：

```lean
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
```

-- To get used to using universal quantifiers, you should try some of the
-- exercises at the end of this section.

为了习惯使用全称量词，你应该尝试本节末尾的一些练习。

:::setup
```
universe i j
variable (α : Sort i) (β : {x : α} → Sort j) {x : α}
```

-- It is the typing rule for dependent arrow types, and the universal
-- quantifier in particular, that distinguishes {lean}`Prop` from other
-- types.  Suppose we have {lean}`α : Sort i` and {lean}`β : Sort j`, where the
-- expression {lean}`β` may depend on a variable {lean}`x : α`. Then
-- {lean}`(x : α) → β` is an element of {lean}`Sort (imax i j)`, where {lit}`imax i j` is the
-- maximum of {lit}`i` and {lit}`j` if {lit}`j` is not {lit}`0`, and {lit}`0` otherwise.

正是依值箭头类型的类型规则，特别是全称量词，将 {lean}`Prop` 与其他类型区分开来。假设我们有 {lean}`α : Sort i` 和 {lean}`β : Sort j`，其中表达式 {lean}`β` 可能取决于变量 {lean}`x : α`。那么 {lean}`(x : α) → β` 是 {lean}`Sort (imax i j)` 的一个元素，其中 {lit}`imax i j` 是 {lit}`i` 和 {lit}`j` 的最大值（如果 {lit}`j` 不是 {lit}`0`），否则为 {lit}`0`。

-- The idea is as follows. If {lit}`j` is not {lit}`0`, then {lean}`(x : α) → β` is
-- an element of {lean}`Sort (max i j)`. In other words, the type of
-- dependent functions from {lean}`α` to {lean}`β` “lives” in the universe whose
-- index is the maximum of {lit}`i` and {lit}`j`. Suppose, however, that {lean}`β`
-- is of {lean}`Sort 0`, that is, an element of {lean}`Prop`. In that case,
-- {lean}`(x : α) → β` is an element of {lean}`Sort 0` as well, no matter which
-- type universe {lean}`α` lives in. In other words, if {lean}`β` is a
-- proposition depending on {lean}`α`, then {lean}`∀ x : α, β` is again a
-- proposition. This reflects the interpretation of {lean}`Prop` as the type
-- of propositions rather than data, and it is what makes {lean}`Prop`
-- {deftech}_impredicative_.

其思想如下。如果 {lit}`j` 不是 {lit}`0`，那么 {lean}`(x : α) → β` 是 {lean}`Sort (max i j)` 的一个元素。换句话说，从 {lean}`α` 到 {lean}`β` 的依值函数类型「生活」在索引为 {lit}`i` 和 {lit}`j` 的最大值的宇宙中。然而，假设 {lean}`β` 是 {lean}`Sort 0` 的，即 {lean}`Prop` 的一个元素。在这种情况下，无论 {lean}`α` 生活在哪个类型宇宙中，{lean}`(x : α) → β` 也是 {lean}`Sort 0` 的一个元素。换句话说，如果 {lean}`β` 是取决于 {lean}`α` 的命题，那么 {lean}`∀ x : α, β` 仍然是一个命题。这反映了将 {lean}`Prop` 解释为命题类型而非数据类型，这也是使 {lean}`Prop` 具有 {deftech}_非直谓性_（impredicative） 的原因。

-- The term “{deftech}[predicative]” stems from foundational developments around the
-- turn of the twentieth century, when logicians such as Poincaré and
-- Russell blamed set-theoretic paradoxes on the “vicious circles” that
-- arise when we define a property by quantifying over a collection that
-- includes the very property being defined. Notice that if {lean}`α` is any
-- type, we can form the type {lean}`α → Prop` of all predicates on {lean}`α`
-- (the “power type of {lean}`α`”). The impredicativity of {lean}`Prop` means that we
-- can form propositions that quantify over {lean}`α → Prop`. In particular,

术语「{deftech}[谓词性]（predicative）」源于 20 世纪初的基础发展，当时庞加莱（Poincaré）和罗素（Russell）等逻辑学家将集合论悖论归咎于「恶性循环」，即当我们通过对包含正在定义的属性本身的集合进行量化来定义该属性时，就会产生这种循环。请注意，如果 {lean}`α` 是任何类型，我们可以形成 {lean}`α` 上所有谓词的类型 {lean}`α → Prop`（{lean}`α` 的「幂类型」）。{lean}`Prop` 的非直谓性意味着我们可以形成对 {lean}`α → Prop` 进行量化的命题。特别是，

-- we can define predicates on {lean}`α` by quantifying over all predicates
-- on {lean}`α`, which is exactly the type of circularity that was once
-- considered problematic.

我们可以通过对 {lean}`α` 上的所有谓词进行量化来定义 {lean}`α` 上的谓词，这正是曾经被认为有问题的那种循环。
:::

-- # Equality
# 相等
%%%
tag := "equality"
%%%

-- Let us now turn to one of the most fundamental relations defined in
-- Lean's library, namely, the equality relation. In the chapter on {ref "inductive-types"}[inductive types],
-- we will explain _how_ equality is defined from the primitives of Lean's logical framework.
-- In the meanwhile, here we explain how to use it.

现在让我们转向 Lean 库中定义的最基本的关系之一，即相等关系。在关于 {ref "inductive-types"}[归纳类型] 的章节中，我们将解释如何从 Lean 逻辑框架的原语中定义相等。与此同时，在这里我们解释如何使用它。

-- Of course, a fundamental property of equality is that it is an equivalence relation:

当然，相等的一个基本性质是它是一个等价关系：

```lean
#check Eq.refl    -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a

#check Eq.symm    -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a

#check Eq.trans   -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c
```

-- We can make the output easier to read by telling Lean not to insert
-- the implicit arguments (which are displayed here as metavariables).

我们可以通过告诉 Lean 不要插入隐式参数（在这里显示为元变量）来使输出更容易阅读。

```lean
universe u

#check @Eq.refl.{u}   -- @Eq.refl : ∀ {α : Sort u} (a : α), a = a

#check @Eq.symm.{u}   -- @Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a

#check @Eq.trans.{u}  -- @Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
```

-- The inscription {lit}`.{u}` tells Lean to instantiate the constants at the universe {lit}`u`.

标记 {lit}`.{u}` 告诉 Lean 在宇宙 {lit}`u` 实例化常量。

-- Thus, for example, we can specialize the example from the previous section to the equality relation:

因此，例如，我们可以将上一节中的示例专门用于相等关系：

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```

-- We can also use the projection notation:

我们也可以使用投影记法：

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)
------
example : a = d := (hab.trans hcb.symm).trans hcd
```

-- Reflexivity is more powerful than it looks. Recall that terms in the
-- Calculus of Constructions have a computational interpretation, and
-- that the logical framework treats terms with a common reduct as the
-- same. As a result, some nontrivial identities can be proved by
-- reflexivity:

自反性比看起来更强大。回想一下，构造演算中的项具有计算解释，并且逻辑框架将具有共同归约结果的项视为相同。因此，一些非平凡的恒等式可以通过自反性来证明：

```lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

-- This feature of the framework is so important that the library defines a notation {lean}`rfl` for {lean}`Eq.refl _`:

框架的这一特性非常重要，以至于库为 {lean}`Eq.refl _` 定义了一个记法 {lean}`rfl`：

```lean
variable (α β : Type)
------
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

:::setup
```
variable {a b : α} {p : α → Prop} {h1 : a = b} {h2 : p a}
```

-- Equality is much more than an equivalence relation, however. It has
-- the important property that every assertion respects the equivalence,
-- in the sense that we can substitute equal expressions without changing
-- the truth value. That is, given {lean}`h1 : a = b` and {lean}`h2 : p a`, we
-- can construct a proof for {lean}`p b` using substitution:
-- {lean}`Eq.subst h1 h2`.

然而，相等不仅仅是一个等价关系。它具有一个重要的性质，即每个断言都遵循这种等价性，也就是说，我们可以替换相等的表达式而不改变真值。也就是说，给定 {lean}`h1 : a = b` 和 {lean}`h2 : p a`，我们可以使用替换构造 {lean}`p b` 的证明：{lean}`Eq.subst h1 h2`。
:::

```lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```

-- The triangle in the second presentation is a macro built on top of
-- {lean}`Eq.subst` and {lean}`Eq.symm`, and you can enter it by typing {kbd}`\t`.

第二个演示中的三角形是建立在 {lean}`Eq.subst` 和 {lean}`Eq.symm` 之上的宏，你可以通过输入 {kbd}`\t` 来输入它。

-- The rule {lean}`Eq.subst` is used to define the following auxiliary rules,
-- which carry out more explicit substitutions. They are designed to deal
-- with applicative terms, that is, terms of form {lean}`s t`. Specifically,
-- {lean}`congrArg` can be used to replace the argument, {lean}`congrFun` can be
-- used to replace the term that is being applied, and {lean}`congr` can be
-- used to replace both at once.

规则 {lean}`Eq.subst` 用于定义以下辅助规则，这些规则执行更显式的替换。它们旨在处理应用项，即形式为 {lean}`s t` 的项。具体来说，{lean}`congrArg` 可用于替换参数，{lean}`congrFun` 可用于替换正在应用的项，而 {lean}`congr` 可用于同时替换两者。

```lean
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁
```

-- Lean's library contains a large number of common identities, such as these:

Lean 库包含大量的常用恒等式，例如：

```lean
variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
```

-- Note that {lean}`Nat.mul_add` and {lean}`Nat.add_mul` are alternative names
-- for {lean}`Nat.left_distrib` and {lean}`Nat.right_distrib`, respectively.  The
-- properties above are stated for the natural numbers (type {lean}`Nat`).

请注意，{lean}`Nat.mul_add` 和 {lean}`Nat.add_mul` 分别是 {lean}`Nat.left_distrib` 和 {lean}`Nat.right_distrib` 的替代名称。上述性质是针对自然数（类型 {lean}`Nat`）陈述的。

-- Here is an example of a calculation in the natural numbers that uses
-- substitution combined with associativity and distributivity.

下面是一个自然数计算的例子，它使用了替换结合结合律和分配律。

```lean
example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
```

:::setup
```
variable {α : Type u}
```

```lean (show := false)
example {α : Type u} {x y : α} {h : x = y} {p : α → Prop} {e : p x} : p y := h ▸ e
```

-- Notice that the second implicit parameter to {lean}`Eq.subst`, which
-- provides the context in which the substitution is to occur, has type
-- {lean}`α → Prop`.  Inferring this predicate therefore requires an instance
-- of _higher-order unification_. In full generality, the problem of
-- determining whether a higher-order unifier exists is undecidable, and
-- Lean can at best provide imperfect and approximate solutions to the
-- problem. As a result, {lean}`Eq.subst` doesn't always do what you want it
-- to.  The macro {leanRef}`h ▸ e` uses more effective heuristics for computing
-- this implicit parameter, and often succeeds in situations where
-- applying {lean}`Eq.subst` fails.

注意，{lean}`Eq.subst` 的第二个隐式参数（提供进行替换的上下文）的类型为 {lean}`α → Prop`。因此，推断此谓词需要 *高阶合一（higher-order unification）* 的实例。在一般情况下，确定是否存在高阶合一器的问题是不可判定的，Lean 最多只能提供该问题的不完美且近似的解决方案。因此，{lean}`Eq.subst` 并不总是能达到你想要的效果。宏 {leanRef}`h ▸ e` 使用更有效的启发式方法来计算此隐式参数，并且通常在应用 {lean}`Eq.subst` 失败的情况下成功。
:::

-- Because equational reasoning is so common and important, Lean provides
-- a number of mechanisms to carry it out more effectively. The next
-- section offers syntax that allow you to write calculational proofs in
-- a more natural and perspicuous way. But, more importantly, equational
-- reasoning is supported by a term rewriter, a simplifier, and other
-- kinds of automation. The term rewriter and simplifier are described
-- briefly in the next section, and then in greater detail in the next
-- chapter.

由于等式推理非常普遍且重要，Lean 提供了许多机制来更有效地执行它。下一节提供的语法允许你以更自然、更清晰的方式编写计算证明。但更重要的是，等式推理得到了项重写器、简化器和其他自动化工具的支持。项重写器和简化器将在下一节中简要介绍，然后在下一章中进行更详细的介绍。

-- # Calculational Proofs
# 计算证明
%%%
tag := "calculational-proofs"
%%%

-- A calculational proof is just a chain of intermediate results that are
-- meant to be composed by basic principles such as the transitivity of
-- equality. In Lean, a calculational proof starts with the keyword
-- {kw}`calc`, and has the following syntax:

计算证明只是一系列中间结果，这些结果旨在通过基本原理（如相等的传递性）组合而成。在 Lean 中，计算证明以关键字 {kw}`calc` 开始，并具有以下语法：

```
calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
  '_'       'op_2'  <expr>_2  ':='  <proof>_2
  ...
  '_'       'op_n'  <expr>_n  ':='  <proof>_n
```

-- Note that the {kw}`calc` relations all have the same indentation. Each
-- {lit}`<proof>_i` is a proof for {lit}`<expr>_{i-1} op_i <expr>_i`.

注意，{kw}`calc` 关系都具有相同的缩进。每个 {lit}`<proof>_i` 都是 {lit}`<expr>_{i-1} op_i <expr>_i` 的证明。

-- We can also use {lit}`_` in the first relation (right after {lit}`<expr>_0`)
-- which is useful to align the sequence of relation/proof pairs:

我们也可以在第一个关系中（紧跟在 {lit}`<expr>_0` 之后）使用 {lit}`_`，这对于对齐关系/证明对序列很有用：

```
calc <expr>_0
    '_' 'op_1' <expr>_1 ':=' <proof>_1
    '_' 'op_2' <expr>_2 ':=' <proof>_2
    ...
    '_' 'op_n' <expr>_n ':=' <proof>_n
```

-- Here is an example:

这里有一个例子：

```lean
variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
```

-- This style of writing proofs is most effective when it is used in
-- conjunction with the {tactic}`simp` and {tactic}`rw` tactics, which are
-- discussed in greater detail in the next chapter. For example, using
-- {tactic}`rw` for rewrite, the proof above could be written
-- as follows:

这种编写证明的风格在与 {tactic}`simp` 和 {tactic}`rw` 策略结合使用时最有效，这些策略将在下一章中更详细地讨论。例如，使用 {tactic}`rw`（表示重写），上面的证明可以写成如下形式：

```lean
variable (a b c d e : Nat)
------
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

-- Essentially, the {kw}`rw` tactic uses a given equality (which can be a
-- hypothesis, a theorem name, or a complex term) to “rewrite” the
-- goal. If doing so reduces the goal to an identity {lean}`t = t`, the
-- tactic applies reflexivity to prove it.

本质上，{kw}`rw` 策略使用给定的等式（可以是假设、定理名称或复杂项）来「重写」目标。如果这样做将目标归约为恒等式 {lean}`t = t`，则该策略应用自反性来证明它。

-- Rewrites can be applied sequentially, so that the proof above can be
-- shortened to this:

重写可以按顺序应用，因此上面的证明可以缩短为：

```lean
variable (a b c d e : Nat)
------
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

-- Or even this:

甚至可以这样：

```lean
variable (a b c d e : Nat)
------
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
```


-- The {kw}`simp` tactic, instead, rewrites the goal by applying the given
-- identities repeatedly, in any order, anywhere they are applicable in a
-- term. It also uses other rules that have been previously declared to
-- the system, and applies commutativity wisely to avoid looping. As a
-- result, we can also prove the theorem as follows:

相反，{kw}`simp` 策略通过重复应用给定的恒等式来重写目标，可以以任何顺序应用在项中任何适用的地方。它还使用先前向系统声明的其他规则，并明智地应用交换律以避免循环。因此，我们也可以按如下方式证明该定理：

```lean
variable (a b c d e : Nat)
------
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

-- We will discuss variations of {kw}`rw` and {kw}`simp` in the next chapter.

我们将在下一章讨论 {kw}`rw` 和 {kw}`simp` 的变体。

-- The {kw}`calc` command can be configured for any relation that supports
-- some form of transitivity. It can even combine different relations.

{kw}`calc` 命令可以为任何支持某种形式传递性的关系进行配置。它甚至可以组合不同的关系。

```lean
variable (a b c d : Nat)
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
```

-- You can “teach” {kw}`calc` new transitivity theorems by adding new instances
-- of the {lean}`Trans` type class. Type classes are introduced later, but the following
-- small example demonstrates how to extend the {kw}`calc` notation using new {lean}`Trans` instances.

你可以通过添加 {lean}`Trans` 类型类的新实例来「教」{kw}`calc` 新的传递性定理。类型类将在后面介绍，但下面的小例子演示了如何使用新的 {lean}`Trans` 实例扩展 {kw}`calc` 记法。

```lean
def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " | " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x | y   := h₁
    _ = z   := h₂
    _ | 2*z := divides_mul ..
```

-- The example above also makes it clear that you can use {kw}`calc` even if you do not have an infix
-- notation for your relation. Lean already includes the standard Unicode notation for divisibility
-- (using {lit}`∣`, which can be entered as {kbd}`\dvd` or {kbd}`\mid`), so the example above uses the ordinary
-- vertical bar to avoid a conflict. In practice, this is not a good idea, as it risks confusion with
-- the ASCII {lit}`|` used in the {kw}`match`{lit}`  ...  `{kw}`with` expression.

上面的例子也清楚地表明，即使你没有关系的中缀记法，你也可以使用 {kw}`calc`。Lean 已经包含了可整除性的标准 Unicode 记法（使用 {lit}`∣`，可以输入为 {kbd}`\dvd` 或 {kbd}`\mid`），因此上面的例子使用普通的竖线来避免冲突。在实践中，这不是一个好主意，因为它可能与 {kw}`match`{lit}`  ...  `{kw}`with` 表达式中使用的 ASCII {lit}`|` 混淆。

-- With {kw}`calc`, we can write the proof in the last section in a more
-- natural and perspicuous way.

使用 {kw}`calc`，我们可以以一种更自然、更清晰的方式编写上一节中的证明。

```lean
variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              :=
      by rw [←Nat.add_assoc]
```

-- The alternative {kw}`calc` notation is worth considering here. When the
-- first expression is taking this much space, using {lit}`_` in the first
-- relation naturally aligns all relations:

另一种 {kw}`calc` 记法在这里值得考虑。当第一个表达式占用这么多空间时，在第一个关系中使用 {lit}`_` 可以自然地对齐所有关系：

```lean
variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   :=
      by rw [←Nat.add_assoc]
```

-- Here the left arrow before {lean}`Nat.add_assoc` tells rewrite to use the
-- identity in the opposite direction. (You can enter it with {kbd}`\l` or
-- use the ASCII equivalent, {lit}`<-`.) If brevity is what we are after,
-- both {tactic}`rw` and {tactic}`simp` can do the job on their own:

这里 {lean}`Nat.add_assoc` 前面的左箭头告诉重写以相反的方向使用恒等式。（你可以通过 {kbd}`\l` 输入它，或者使用 ASCII 等效项 {lit}`<-`。）如果我们追求简洁，{tactic}`rw` 和 {tactic}`simp` 都可以独立完成工作：

```lean
variable (x y : Nat)
example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y := by
  simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
```

-- # The Existential Quantifier
# 存在量词
%%%
tag := "the-existential-quantifier"
%%%

-- Finally, consider the existential quantifier, which can be written as
-- either {lean}`exists x : α, p x` or {lean}`∃ x : α, p x`.  Both versions are
-- actually notationally convenient abbreviations for a more long-winded
-- expression, {lean}`Exists (fun x : α => p x)`, defined in Lean's library.

最后，考虑存在量词，它可以写成 {lean}`exists x : α, p x` 或 {lean}`∃ x : α, p x`。这两个版本实际上都是 Lean 库中定义的更冗长的表达式 {lean}`Exists (fun x : α => p x)` 的记法上的便利缩写。

-- As you should by now expect, the library includes both an introduction
-- rule and an elimination rule. The introduction rule is
-- straightforward: to prove {lean}`∃ x : α, p x`, it suffices to provide a
-- suitable term {lean}`t` and a proof of {lean}`p t`. Here are some examples:

正如你现在所期望的，库中既包含引入规则也包含消去规则。引入规则很简单：要证明 {lean}`∃ x : α, p x`，只需提供一个合适的项 {lean}`t` 和 {lean}`p t` 的证明。这里有一些例子：

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro -- @Exists.intro : ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p
```

:::setup
```
variable {t : α} {p : α → Prop} (h : p t)
```
-- We can use the anonymous constructor notation {lean (type := "Exists (fun x : α => p x)")}`⟨t, h⟩` for
-- {lean}`Exists.intro t h`, when the type is clear from the context.

当类型从上下文中很清楚时，我们可以为 {lean}`Exists.intro t h` 使用匿名构造器记法 {lean (type := "Exists (fun x : α => p x)")}`⟨t, h⟩`。
:::

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩
```

:::setup
```
variable (p : α → Prop) (g : Nat → Nat → Nat) (hg : g 0 0 = 0)
```

-- Note that {lean}`Exists.intro` has implicit arguments: Lean has to infer
-- the predicate {lean}`p : α → Prop` in the conclusion {lean}`∃ x, p x`.  This
-- is not a trivial affair. For example, if we have
-- {lean}`hg : g 0 0 = 0` and write {lean}`Exists.intro 0 hg`, there are many possible values
-- for the predicate {lean}`p`, corresponding to the theorems {lean}`∃ x, g x x = x`,
-- {lean}`∃ x, g x x = 0`, {lean}`∃ x, g x 0 = x`, etc. Lean uses the
-- context to infer which one is appropriate. This is illustrated in the
-- following example, in which we set the option {option}`pp.explicit` to true
-- to ask Lean's pretty-printer to show the implicit arguments.

注意，{lean}`Exists.intro` 具有隐式参数：Lean 必须在结论 {lean}`∃ x, p x` 中推断谓词 {lean}`p : α → Prop`。这并非易事。例如，如果我们有 {lean}`hg : g 0 0 = 0` 并编写 {lean}`Exists.intro 0 hg`，则谓词 {lean}`p` 有许多可能的值，对应于定理 {lean}`∃ x, g x x = x`、{lean}`∃ x, g x x = 0`、{lean}`∃ x, g x 0 = x` 等。Lean 使用上下文来推断哪一个是合适的。下面的示例说明了这一点，其中我们将选项 {option}`pp.explicit` 设置为 true，以要求 Lean 的漂亮打印机显示隐式参数。
:::

```lean
variable (g : Nat → Nat → Nat)

theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments

#print gex1

#print gex2

#print gex3

#print gex4
```

:::setup
```
variable (q : Prop) (α : Type u) (p : α → Prop) (w : α) (x : α)
```

-- We can view {lean}`Exists.intro` as an information-hiding operation, since
-- it hides the witness to the body of the assertion. The existential
-- elimination rule, {lean}`Exists.elim`, performs the opposite operation. It
-- allows us to prove a proposition {lean}`q` from {lean}`∃ x : α, p x`, by
-- showing that {lean}`q` follows from {lean}`p w` for an arbitrary value
-- {lean}`w`. Roughly speaking, since we know there is an {lean}`x` satisfying
-- {lean}`p x`, we can give it a name, say, {lean}`w`. If {lean}`q` does not mention
-- {lean}`w`, then showing that {lean}`q` follows from {lean}`p w` is tantamount to
-- showing that {lean}`q` follows from the existence of any such {lean}`x`. Here
-- is an example:

我们可以将 {lean}`Exists.intro` 视为一种信息隐藏操作，因为它隐藏了断言主体的见证。存在消去规则 {lean}`Exists.elim` 执行相反的操作。它允许我们通过证明 {lean}`q` 从任意值 {lean}`w` 的 {lean}`p w` 推导出来，从而从 {lean}`∃ x : α, p x` 证明命题 {lean}`q`。粗略地说，既然我们知道存在一个满足 {lean}`p x` 的 {lean}`x`，我们可以给它起个名字，比如 {lean}`w`。如果 {lean}`q` 不涉及 {lean}`w`，那么证明 {lean}`q` 从 {lean}`p w` 推导出来就等同于证明 {lean}`q` 从任何此类 {lean}`x` 的存在性推导出来。这里有一个例子：
:::

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
```

:::setup
```
variable {α : Type u} (p : α → Prop) {β : α → Type} (a : α) (h : p a) (h' : β a)
```

-- It may be helpful to compare the exists-elimination rule to the
-- or-elimination rule: the assertion {lean}`∃ x : α, p x` can be thought of
-- as a big disjunction of the propositions {lean}`p a`, as {lean}`a` ranges over
-- all the elements of {lean}`α`. Note that the anonymous constructor
-- notation {leanRef}`⟨w, hw.right, hw.left⟩` abbreviates a nested constructor
-- application; we could equally well have written {lit}`⟨`{leanRef}`w`{lit}`, ⟨`{leanRef}`hw.right`{lit}`, `{leanRef}`hw.left`{lit}`⟩⟩`.

将存在消去规则与析取消去规则进行比较可能会有所帮助：断言 {lean}`∃ x : α, p x` 可以被视为命题 {lean}`p a` 的巨大析取，其中 {lean}`a` 遍历 {lean}`α` 的所有元素。请注意，匿名构造器记法 {leanRef}`⟨w, hw.right, hw.left⟩` 缩写了嵌套的构造器应用；我们同样可以写成 {lit}`⟨`{leanRef}`w`{lit}`, ⟨`{leanRef}`hw.right`{lit}`, `{leanRef}`hw.left`{lit}`⟩⟩`。

-- Notice that an existential proposition is very similar to a sigma
-- type, as described in dependent types section.  The difference is that
-- existential propositions are _propositions_, while sigma types are _types_.
-- Otherwise, they are very similar. Given a predicate {lean}`p : α → Prop` and a family of types {lean}`β : α → Type`,
-- for a term {lean}`a : α` with {lean}`h : p a` and {lean}`h' : β a`, the term {lean}`Exists.intro a h` has
-- type {lean}`(∃ x : α, p x) : Prop`, while {lean}`Sigma.mk a h'` has type
-- {lean}`(Σ x : α, β x)`. The similarity between {lit}`∃` and {lit}`Σ` is another
-- instance of the {tech}[Curry-Howard isomorphism].

注意，存在命题与依值类型一节中描述的 Sigma 类型非常相似。区别在于存在命题是 *命题（propositions）*，而 Sigma 类型是 *类型（types）*。除此之外，它们非常相似。给定谓词 {lean}`p : α → Prop` 和类型族 {lean}`β : α → Type`，对于具有 {lean}`h : p a` 和 {lean}`h' : β a` 的项 {lean}`a : α`，项 {lean}`Exists.intro a h` 的类型为 {lean}`(∃ x : α, p x) : Prop`，而 {lean}`Sigma.mk a h'` 的类型为 {lean}`(Σ x : α, β x)`。{lit}`∃` 和 {lit}`Σ` 之间的相似性是 {tech}[Curry-Howard 同构] 的另一个例子。
:::

-- Lean provides a more convenient way to eliminate from an existential
-- quantifier with the {kw}`match` expression:

Lean 提供了一种更方便的方法，可以使用 {kw}`match` 表达式从存在量词中消去：

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
```

-- The {kw}`match` expression is part of Lean's function definition system,
-- which provides convenient and expressive ways of defining complex
-- functions.  Once again, it is the {tech}[Curry-Howard isomorphism] that allows
-- us to co-opt this mechanism for writing proofs as well.  The {kw}`match`
-- statement “destructs” the existential assertion into the components
-- {leanRef}`w` and {leanRef}`hw`, which can then be used in the body of the statement
-- to prove the proposition. We can annotate the types used in the match
-- for greater clarity:

{kw}`match` 表达式是 Lean 函数定义系统的一部分，它提供了方便且富有表现力的方式来定义复杂函数。再一次，正是 {tech}[Curry-Howard 同构] 允许我们也将这种机制用于编写证明。{kw}`match` 语句将存在断言「解构」为组件 {leanRef}`w` 和 {leanRef}`hw`，然后可以在语句主体中使用它们来证明命题。为了更清晰起见，我们可以对 match 中使用的类型进行注释：

```lean
variable (α : Type) (p q : α → Prop)
------
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
```

-- We can even use the match statement to decompose the conjunction at the same time:

我们甚至可以使用 match 语句同时分解合取式：

```lean
variable (α : Type) (p q : α → Prop)
------
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

-- Lean also provides a pattern-matching {kw}`let` expression:

Lean 还提供了一个模式匹配 {kw}`let` 表达式：

```lean
variable (α : Type) (p q : α → Prop)
------
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

-- This is essentially just alternative notation for the {kw}`match`
-- construct above. Lean will even allow us to use an implicit {kw}`match`
-- in the {kw}`fun` expression:

这本质上只是上述 {kw}`match` 结构的替代记法。Lean 甚至允许我们在 {kw}`fun` 表达式中使用隐式 {kw}`match`：

```lean
variable (α : Type) (p q : α → Prop)
------
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

-- We will see in {ref "induction-and-recursion"}[Induction and Recursion] that all these variations are
-- instances of a more general pattern-matching construct.

我们将在 {ref "induction-and-recursion"}[归纳与递归] 中看到，所有这些变体都是更通用的模式匹配结构的实例。

:::setup
```
def IsEven (a : Nat) := ∃ b, a = 2 * b
variable (a : Nat)
```

-- In the following example, we define {lean}`IsEven a` as {lean}`∃ b, a = 2 * b`,
-- and then we show that the sum of two even numbers is an even number.

```lean
def IsEven (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))
```

在下面的例子中，我们将 {lean}`IsEven a` 定义为 {lean}`∃ b, a = 2 * b`，然后证明两个偶数之和是一个偶数。
:::

-- Using the various gadgets described in this chapter—the match
-- statement, anonymous constructors, and the {tactic}`rewrite` tactic, we can
-- write this proof concisely as follows:

使用本章中描述的各种工具：match 语句、匿名构造器和 {tactic}`rewrite` 策略，我们可以简洁地编写此证明如下：

```lean
def IsEven (a : Nat) := ∃ b, a = 2 * b
------
theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
```

:::leanFirst
-- Just as the constructive “or” is stronger than the classical “or,” so,
-- too, is the constructive “exists” stronger than the classical
-- “exists”. For example, the following implication requires classical
-- reasoning because, from a constructive standpoint, knowing that it is
-- not the case that every {leanRef}`x` satisfies {leanRef}`¬ p` is not the same as
-- having a particular {leanRef}`x` that satisfies {leanRef}`p`.

正如构造性的「或」比经典逻辑的「或」更强一样，构造性的「存在」也比经典逻辑的「存在」更强。例如，下面的蕴涵式需要经典推理，因为从构造性的观点来看，知道并非每个 {leanRef}`x` 都满足 {leanRef}`¬ p` 并不等同于拥有一个满足 {leanRef}`p` 的特定 {leanRef}`x`。

```lean
open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)
```
:::

-- What follows are some common identities involving the existential
-- quantifier. In the exercises below, we encourage you to prove as many
-- as you can. We also leave it to you to determine which are
-- nonconstructive, and hence require some form of classical reasoning.

接下来是一些涉及存在量词的常见恒等式。在下面的练习中，我们鼓励你尽可能多地证明它们。我们还留给你去确定哪些是非构造性的，因此需要某种形式的经典推理。

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
```

-- Notice that the second example and the last two examples require the
-- assumption that there is at least one element {leanRef}`a` of type {leanRef}`α`.

注意，第二个例子和最后两个例子需要假设类型 {leanRef}`α` 至少有一个元素 {leanRef}`a`。

-- Here are solutions to two of the more difficult ones:

这里是其中两个较难问题的解答：

```lean
open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
```

-- # More on the Proof Language
# 更多关于证明语言的内容
%%%
tag := "more-on-the-proof-language"
%%%

-- We have seen that keywords like {kw}`fun`, {kw}`have`, and {kw}`show` make
-- it possible to write formal proof terms that mirror the structure of
-- informal mathematical proofs. In this section, we discuss some
-- additional features of the proof language that are often convenient.

我们已经看到，像 {kw}`fun`、{kw}`have` 和 {kw}`show` 这样的关键字使得编写反映非正式数学证明结构的正式证明项成为可能。在本节中，我们将讨论证明语言的一些通常很方便的其他特性。

-- To start with, we can use anonymous {kw}`have` expressions to introduce an
-- auxiliary goal without having to label it. We can refer to the last
-- expression introduced in this way using the keyword {lit}`this`:

首先，我们可以使用匿名 {kw}`have` 表达式来引入辅助目标，而无需对其进行标记。我们可以使用关键字 {lit}`this` 来引用以这种方式引入的最后一个表达式：

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
```

-- Often proofs move from one fact to the next, so this can be effective
-- in eliminating the clutter of lots of labels.

通常证明从一个事实移动到下一个事实，因此这可以有效地消除大量标签带来的混乱。

-- When the goal can be inferred, we can also ask Lean instead to fill in
-- the proof by writing {kw}`by assumption`:

当目标可以推断出来时，我们也可以要求 Lean 通过编写 {kw}`by assumption` 来填充证明：

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))
------
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
```

-- This tells Lean to use the {leanRef}`assumption` tactic, which, in turn,
-- proves the goal by finding a suitable hypothesis in the local
-- context. We will learn more about the {leanRef}`assumption` tactic in the
-- next chapter.

这告诉 Lean 使用 {leanRef}`assumption` 策略，该策略反过来通过在本地上下文中查找合适的假设来证明目标。我们将在下一章中详细了解 {leanRef}`assumption` 策略。

:::setup
```
variable {p : Prop} (prf : p)
```
-- We can also ask Lean to fill in the proof by writing {lean}`‹p›`, where
-- {lean}`p` is the proposition whose proof we want Lean to find in the
-- context.  You can type these corner quotes using {kbd}`\f<` and {kbd}`\f>`,
-- respectively. The letter “f” is for “French,” since the Unicode
-- symbols can also be used as French quotation marks. In fact, the
-- notation is defined in Lean as follows:

我们还可以通过编写 {lean}`‹p›` 来要求 Lean 填充证明，其中 {lean}`p` 是我们希望 Lean 在上下文中找到其证明的命题。你可以分别使用 {kbd}`\f<` 和 {kbd}`\f>` 输入这些角引号。字母「f」代表「French（法语）」，因为 Unicode 符号也可以用作法语引号。事实上，该记法在 Lean 中定义如下：
:::

```lean
notation "‹" p "›" => show p by assumption
```

-- This approach is more robust than using {leanRef}`by assumption`, because the
-- type of the assumption that needs to be inferred is given
-- explicitly. It also makes proofs more readable. Here is a more
-- elaborate example:

这种方法比使用 {leanRef}`by assumption` 更健壮，因为需要推断的假设类型是显式给出的。它还使证明更具可读性。这里有一个更详细的例子：

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
```

-- Keep in mind that you can use the French quotation marks in this way
-- to refer to _anything_ in the context, not just things that were
-- introduced anonymously. Its use is also not limited to propositions,
-- though using it for data is somewhat odd:

请记住，你可以以这种方式使用法语引号来引用上下文中的 *任何内容*，而不仅仅是匿名引入的内容。它的用途也不限于命题，尽管将其用于数据有些奇怪：

```lean
example (n : Nat) : Nat := ‹Nat›
```

-- Later, we show how you can extend the proof language using the Lean macro system.

稍后，我们将展示如何使用 Lean 宏系统扩展证明语言。

-- # Exercises
# 练习
%%%
tag := "quantifiers-and-equality-exercises"
%%%

-- 1. Prove these equivalences:

1. 证明这些等价式：

    ```lean
    variable (α : Type) (p q : α → Prop)

    example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
    example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
    example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
    ```

--   You should also try to understand why the reverse implication is not derivable in the last example.

你还应该试着理解为什么在最后一个例子中反向蕴涵是不可导出的。

-- 2. It is often possible to bring a component of a formula outside a
--    universal quantifier, when it does not depend on the quantified
--    variable. Try proving these (one direction of the second of these
--    requires classical logic):

2. 当公式的一个组件不依赖于量化变量时，通常可以将其移到全称量词之外。尝试证明这些（其中第二个的一个方向需要经典逻辑）：

    ```lean
    variable (α : Type) (p q : α → Prop)
    variable (r : Prop)

    example : α → ((∀ x : α, r) ↔ r) := sorry
    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
    ```

-- 3. Consider the “barber paradox,” that is, the claim that in a certain
--    town there is a (male) barber that shaves all and only the men who
--    do not shave themselves. Prove that this is a contradiction:

3. 考虑「理发师悖论」，即声称在某个小镇上有一个（男）理发师，他只给所有不给自己刮胡子的男人刮胡子。证明这是一个矛盾：

    ```lean
    variable (men : Type) (barber : men)
    variable (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
      sorry
    ```

-- 4. Remember that, without any parameters, an expression of type
--    {lean}`Prop` is just an assertion. Fill in the definitions of {leanRef}`prime`
--    and {leanRef}`Fermat_prime` below, and construct each of the given
--    assertions. For example, you can say that there are infinitely many
--    primes by asserting that for every natural number {lean}`n`, there is a
--    prime number greater than {lean}`n`. Goldbach's weak conjecture states
--    that every odd number greater than 5 is the sum of three
--    primes. Look up the definition of a Fermat prime or any of the
--    other statements, if necessary.

4. ::::setup
   ```
   variable {n : Nat}
   ```
   :::leanFirst
   记住，在没有任何参数的情况下，{lean}`Prop` 类型的表达式只是一个断言。填写下面 {leanRef}`prime` 和 {leanRef}`Fermat_prime` 的定义，并构造每个给定的断言。例如，你可以通过断言对于每个自然数 {lean}`n`，都存在一个大于 {lean}`n` 的素数来表示有无穷多个素数。哥德巴赫弱猜想（Goldbach's weak conjecture）指出，每个大于 5 的奇数都是三个素数之和。如果有必要，请查阅费马素数（Fermat prime）的定义或任何其他陈述。

    ```lean
    def even (n : Nat) : Prop := sorry

    def prime (n : Nat) : Prop := sorry

    def infinitely_many_primes : Prop := sorry

    def Fermat_prime (n : Nat) : Prop := sorry

    def infinitely_many_Fermat_primes : Prop := sorry

    def goldbach_conjecture : Prop := sorry

    def Goldbach's_weak_conjecture : Prop := sorry

    def Fermat's_last_theorem : Prop := sorry
    ```
   :::
   ::::

-- 5. Prove as many of the identities listed in the Existential
--    Quantifier section as you can.

5. 尽可能多地证明「存在量词」一节中列出的恒等式。
