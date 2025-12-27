import VersoManual
import TPiLZh.Examples

open Verso.Genre Manual
open TPiLZh

set_option linter.typography.dashes false

#doc (Manual) "公理与计算" =>
%%%
tag := "axioms-and-computation"
file := "AxiomsComputation"
%%%
-- Axioms and Computation

-- We have seen that the version of the Calculus of Constructions that
-- has been implemented in Lean includes dependent function types,
-- inductive types, and a hierarchy of universes that starts with an
-- {tech}[impredicative], {tech (key := "proof irrelevance")}[proof-irrelevant] {lean}`Prop` at the bottom. In this
-- chapter, we consider ways of extending the CIC with additional axioms
-- and rules. Extending a foundational system in such a way is often
-- convenient; it can make it possible to prove more theorems, as well as
-- make it easier to prove theorems that could have been proved
-- otherwise. But there can be negative consequences of adding additional
-- axioms, consequences which may go beyond concerns about their
-- correctness. In particular, the use of axioms bears on the
-- computational content of definitions and theorems, in ways we will
-- explore here.

我们已经看到 Lean 中实现的构造演算的版本包括有：依值函数类型、
归纳类型以及一个满足 {tech}[非直谓性] 和 {tech}[证明无关性] 的 {lean}`Prop` 为底层的宇宙层级。
在本章中，我们要探讨使用附加公理和规则扩展 CIC 的方法。
用这种方式扩展一个基础系统通常很方便；它可以使得证明更多的定理成为可能，
并使得证明原本可以被证明的定理变得更容易。但是，添加附加公理可能会产生负面后果，
这些后果可能超出了人们对它们的正确性的担忧。
特别是，公理的使用会以我们将在本文中探究的方式，对定义和定理的计算内容产生影响。

-- Lean is designed to support both computational and classical
-- reasoning. Users that are so inclined can stick to a “computationally
-- pure” fragment, which guarantees that closed expressions in the system
-- evaluate to canonical normal forms. In particular, any closed
-- computationally pure expression of type {lean}`Nat`, for example, will
-- reduce to a numeral.

Lean 被设计为支持计算推理和经典推理。有此需求的用户可坚持使用“计算上纯粹”的片段，
它可以确保系统中的封闭表达式会求值为标准范式。具体说来，任何类型为 {lean}`Nat`
的封闭计算上纯粹表达式最终都将归约为一个数值。

-- Lean's standard library defines an additional axiom, propositional
-- extensionality, and a quotient construction which in turn implies the
-- principle of function extensionality. These extensions are used, for
-- example, to develop theories of sets and finite sets. We will see
-- below that using these theorems can block evaluation in Lean's kernel,
-- so that closed terms of type {lean}`Nat` no longer evaluate to numerals. But
-- Lean erases types and propositional information when compiling
-- definitions to executable code, and since
-- these axioms only add new propositions, they are compatible with that
-- computational interpretation. Even computationally inclined users may
-- wish to use the classical law of the excluded middle to reason about
-- computation. This also blocks evaluation in the kernel, but it is
-- compatible with compiled code.

Lean 的标准库定义了一个公理：*命题外延性（Propositional Extensionality）*。
以及一个*商（Quotient）*结构，它蕴含了函数外延性的公理。
这些扩展被用来发展如集合与有限集这些理论。我们在后面会看到，
这些定理的使用会阻碍 Lean 内核中的求值，因此 {lean}`Nat` 类型的封闭项不再求值为数值。
但是 Lean 在将定义编译为可执行代码时会擦除类型和命题信息，
并且由于这些公理只增加了新的命题，它们与这种计算解释是相容的。
即使是倾向于可计算性的用户也可能希望使用排中律来推理计算。
这也会阻碍内核中的求值，但它与编译后的代码是兼容的。

-- The standard library also defines a choice principle that is entirely
-- antithetical to a computational interpretation, since it magically
-- produces “data” from a proposition asserting its existence. Its use is
-- essential to some classical constructions, and users can import it
-- when needed. But expressions that use this construction to produce
-- data do not have computational content, and in Lean we are required to
-- mark such definitions as {kw}`noncomputable` to flag that fact.

标准函数库还定义了一个选择公理（Choice Principle），该公理与计算诠释完全相反，
因为它神奇地根据断言自身存在的命题产生“数据”。
它对于一些经典结构来说是必不可少的，用户可以在需要时导入它。
但使用此构造来产生数据的表达式将不存在计算内容，
在 Lean 中我们需要将此类定义标记为 {kw}`noncomputable`（不可计算的）以表明该事实。

-- Using a clever trick (known as Diaconescu's theorem), one can use
-- propositional extensionality, function extensionality, and choice to
-- derive the law of the excluded middle. As noted above, however, use of
-- the law of the excluded middle is still compatible with
-- compilation, as are other classical principles, as
-- long as they are not used to manufacture data.

使用一个巧妙的技巧（称为狄阿科涅斯库定理），人们可以使用命题外延性、
函数外延性和选择公理来导出排中律。然而，如上所述，使用排中律仍然兼容编译，
就像其他经典公理一样，只要它们不被用来制造数据。

-- To summarize, then, on top of the underlying framework of universes,
-- dependent function types, and inductive types, the standard library
-- adds three additional components:

-- - the axiom of propositional extensionality
-- - a quotient construction, which implies function extensionality
-- - a choice principle, which produces data from an existential proposition.

-- The first two of these block normalization within Lean, but are
-- compatible with code generation, whereas the third is not amenable
-- to computational interpretation. We will spell out the details more
-- precisely below.

总而言之，在我们的宇宙类型，依值函数类型和归纳类型的底层框架之上，
标准库增加了三个附加元素：

- 命题外延性公理
- 蕴含了函数外延性的的商构造
- 选择公理，它从存在命题中产生数据。

前两项在 Lean 中对这些块标准化，但与代码生成兼容，
而第三项不适合可计算性解释。我们将在下面更精确地说明这些细节。

-- # Historical and Philosophical Context
# 历史与哲学背景
%%%
tag := "historical-and-philosophical-context"
%%%

:::setup
```
variable (x : α) (y : β)
```

-- For most of its history, mathematics was essentially computational:
-- geometry dealt with constructions of geometric objects, algebra was
-- concerned with algorithmic solutions to systems of equations, and
-- analysis provided means to compute the future behavior of systems
-- evolving over time. From the proof of a theorem to the effect that
-- “for every {lean}`x`, there is a {lean}`y` such that ...”, it was generally
-- straightforward to extract an algorithm to compute such a {lean}`y` given
-- {lean}`x`.

历史上大部分时候，数学主要是计算性的：几何处理涉及几何对象的构造，
代数涉及方程组的算法解，分析提供了计算系统随时间演变的未来行为的方法。
从定理的证明到“对于每个 {lean}`x`，都有一个 {lean}`y` 使得 ...”这一效果，
通常可以提取一种算法来根据给定的 {lean}`x` 计算这样的的 {lean}`y`。
:::

-- In the nineteenth century, however, increases in the complexity of
-- mathematical arguments pushed mathematicians to develop new styles of
-- reasoning that suppress algorithmic information and invoke
-- descriptions of mathematical objects that abstract away the details of
-- how those objects are represented. The goal was to obtain a powerful
-- “conceptual” understanding without getting bogged down in
-- computational details, but this had the effect of admitting
-- mathematical theorems that are simply _false_ on a direct
-- computational reading.

然而在 19 世纪，数学论证复杂性的提升推动了数学家发展新的推理风格，
抑制算法信息并调用数学对象，从而抽象掉了对象被表征的细节。
目标是在不陷入繁重的计算细节的情况下获得强大的“概念”理解，
但这可能导致数学定理在直接计算的解读上干脆就是 _错误_ 的。

-- There is still fairly uniform agreement today that computation is
-- important to mathematics. But there are different views as to how best
-- to address computational concerns. From a _constructive_ point of
-- view, it is a mistake to separate mathematics from its computational
-- roots; every meaningful mathematical theorem should have a direct
-- computational interpretation. From a _classical_ point of view, it is
-- more fruitful to maintain a separation of concerns: we can use one
-- language and body of methods to write computer programs, while
-- maintaining the freedom to use nonconstructive theories and methods
-- to reason about them. Lean is designed to support both of these
-- approaches. Core parts of the library are developed constructively,
-- but the system also provides support for carrying out classical
-- mathematical reasoning.

今天数学界仍在相当普遍地同意计算对于数学很重要。
但对于如何以最佳方式解决计算问题有不同的看法。
从 _构造性_ 的角度来看，将数学与其计算根源分开是一个错误；
每条有意义的数学定理都应具有直接的计算解释。
从 _经典的_ 角度来看，保持关注点的分离更有成效：
我们可以使用一种语言和方法体系编写计算机程序，
同时保持使用非构造性理论和方法对其进行推理的自由。
Lean 旨在支持这两种方法。库的核心部分以构造性方式开发，
但该系统还提供了支持进行经典数学推理的支持。

:::setup
```
open Nat
notation "… " e "…" => e
```

-- Computationally, the purest part of dependent type theory avoids the
-- use of {lean}`Prop` entirely. Inductive types and dependent function types
-- can be viewed as data types, and terms of these types can be
-- “evaluated” by applying reduction rules until no more rules can be
-- applied. In principle, any closed term (that is, term with no free
-- variables) of type {lean}`Nat` should evaluate to a numeral, {lean}`succ (… (succ zero)…)`.

从计算的角度来看，依值类型论中最纯粹的部分完全避免使用 {lean}`Prop`。
归纳类型和依值函数类型可以看作是数据类型，这些类型的项可以通过应用归约规则进行“求值”，
直到不能再应用任何规则为止。原则上，类型为 {lean}`Nat` 的任何封闭项（即没有自由变量的项）
都应求值为一个数值：{lean}`succ (… (succ zero)…)`。
:::

:::setup
```
variable (p : Prop) (s t : α) (prf : p)
notation x " = " y " : " α => @Eq α x y
```

-- Introducing a proof-irrelevant {lean}`Prop` and marking theorems
-- irreducible represents a first step towards separation of
-- concerns. The intention is that elements of a type {lean}`p : Prop` should
-- play no role in computation, and so the particular construction of a
-- term {lean}`prf : p` is “irrelevant” in that sense. One can still define
-- computational objects that incorporate elements of type {lean}`Prop`; the
-- point is that these elements can help us reason about the effects of
-- the computation, but can be ignored when we extract “code” from the
-- term. Elements of type {lean}`Prop` are not entirely innocuous,
-- however. They include equations {lean}`s = t : α` for any type {lean}`α`, and
-- such equations can be used as casts, to type check terms. Below, we
-- will see examples of how such casts can block computation in the
-- system. However, computation is still possible under an evaluation
-- scheme that erases propositional content, ignores intermediate typing
-- constraints, and reduces terms until they reach a normal form. This is
-- precisely what Lean's virtual machine does.

引入一个与证明无关的 {lean}`Prop` 并标记定理不可约表示了分离关注点的第一步。
目的是类型为 {lean}`p : Prop` 的元素在计算中不应发挥任何作用，因此从这个意义上说，
项 {lean}`prf : p` 的特定构造是“无关的”。人们仍然可以定义包含类型为 {lean}`Prop`
的元素的计算对象；关键是这些元素可以帮助我们推理计算的影响，
但在我们从项中提取“代码”时可以忽略。但是，{lean}`Prop` 类型的元素并非完全无害。
它们包括任何类型 {lean}`α` 的方程 {lean}`s = t : α`，并且此类方程可以作为强制转换使用，
以对项进行类型检查。在后面，我们将看到此类强制转换是如何阻碍系统中的计算的示例。
但是，在擦除命题内容、忽略中间定型约束并归约项，直到它们达到正规形式的求值方案下，
它们仍然可以进行计算。这正是 Lean 的虚拟机所做的。

-- Having adopted a proof-irrelevant {lean}`Prop`, one might consider it
-- legitimate to use, for example, the law of the excluded middle,
-- {lean}`p ∨ ¬p`, where {lean}`p` is any proposition. Of course, this, too, can block
-- computation according to the rules of CIC, but it does not prevent the generation
-- of executable code, as described above. It is only the choice
-- principles discussed in {ref "choice"}[the section on choice] that completely erase the
-- distinction between the proof-irrelevant and data-relevant parts of
-- the theory.


在通过了证明无关的 {lean}`Prop` 之后，可以认为使用排中律 {lean}`p ∨ ¬p` 是合法的，
其中 {lean}`p` 是任何命题。当然，这也可能根据 CIC 的规则阻止计算，
但它不会阻止可执行代码的生成，如上所述。仅在{ref "choice"}[关于选择的章节]
中讨论过的选择原则才能完全消除理论中与证明无关的部分和与数据相关部分之间的区别。

:::

-- # Propositional Extensionality
# 命题外延性
%%%
tag := "propositional-extensionality"
%%%

-- Propositional extensionality is the following axiom:

命题外延性公理如下：

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
axiom propext {a b : Prop} : (a ↔ b) → a = b
------
end Hidden
```

:::setup
```
variable (a : Prop)
```
-- It asserts that when two propositions imply one another, they are
-- actually equal. This is consistent with set-theoretic interpretations
-- in which any element {lean}`a : Prop` is either empty or the singleton set
-- $`\{\ast\}`, for some distinguished element $`\ast`. The axiom has the
-- effect that equivalent propositions can be substituted for one another
-- in any context:

它断言当两个命题互相蕴含时，二者实质相等。这与集合论的解释一致，
即对于某个特定的元素 $`\ast`，其中任何元素 {lean}`a : Prop` 要么为空集，
要么是单元素集 $`\{\ast\}`。此公理具有这样的效果，即等价的命题可以在任何语境中彼此替换：
:::

```lean
variable (a b c d e : Prop)

theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁
```

:::comment
```
<!--
The first example could be proved more laboriously without `propext`
using the fact that the propositional connectives respect
propositional equivalence. The second example represents a more
essential use of `propext`. In fact, it is equivalent to `propext`
itself, a fact which we encourage you to prove.

Given any definition or theorem in Lean, you can use the ``#print
axioms`` command to display the axioms it depends on.

.. code-block:: lean

    variables a b c d e : Prop
    variable p : Prop → Prop

    theorem thm₁ (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
    propext h ▸ iff.refl _

    theorem thm₂ (h : a ↔ b) (h₁ : p a) : p b :=
    propext h ▸ h₁

    -- BEGIN
    #print axioms thm₁  -- propext
    #print axioms thm₂  -- propext
    -- END
-->
```
:::

-- # Function Extensionality
# 函数外延性
%%%
tag := "function-extensionality"
%%%

:::leanFirst
-- Similar to propositional extensionality, function extensionality
-- asserts that any two functions of type {leanRef}`(x : α) → β x` that agree on
-- all their inputs are equal:

Similar to propositional extensionality, function extensionality
asserts that any two functions of type {leanRef}`(x : α) → β x` that agree on
all their inputs are equal:

```signature
funext.{u, v}
  {α : Sort u} {β : α → Sort v}
  {f g : (x : α) → β x}
  (h : ∀ (x : α), f x = g x) :
  f = g
```

与命题外延性类似，函数外延性断言任何两个类型为 {leanRef}`(x : α) → β x`
的函数，如果它们在所有输入上都一致，那么它们就是相等的：
:::

-- From a classical, set-theoretic perspective, this is exactly what it
-- means for two functions to be equal. This is known as an “extensional”
-- view of functions. From a constructive perspective, however, it is
-- sometimes more natural to think of functions as algorithms, or
-- computer programs, that are presented in some explicit way. It is
-- certainly the case that two computer programs can compute the same
-- answer for every input despite the fact that they are syntactically
-- quite different. In much the same way, you might want to maintain a
-- view of functions that does not force you to identify two functions
-- that have the same input / output behavior. This is known as an
-- “intensional” view of functions.

从经典的集合论角度来看，这正是两个函数相等的确切含义。
它被称作函数的“外延性（Extensional）”视角。然而，从构造主义的角度来看，
有时把函数看作算法，或者以某种明确的方式给出的计算机程序要更加自然。
肯定存在这样的情况：两个计算机程序对每个输入都计算出相同的答案，
尽管它们在语法上非常不同。与此类似，你可能想要维护一种函数的视角，
它不会强迫你将具有相同输入/输出行为的两个函数认定为同样的。
这被称为函数的“内涵（Intensional）”视角。

-- In fact, function extensionality follows from the existence of
-- quotients, which we describe in the next section. In the Lean standard
-- library, therefore, {leanRef}`funext` is thus
-- [proved from the quotient construction](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean).

实际上，函数外延性来自于商的存在，我们将在下一节中进行描述。
因此，在 Lean 标准库中，{leanRef}`funext` 通过[商的构造来证明](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean)。

:::leanFirst
-- Suppose that for {leanRef}`α : Type u` we define the {leanRef}`Set `{leanRef (in := "(α : Type u)")}`α`{leanRef}` := α → Prop` to
-- denote the type of subsets of {leanRef (in := "(α : Type u)")}`α`, essentially identifying subsets
-- with predicates. By combining {leanRef}`funext` and {leanRef}`propext`, we obtain an
-- extensional theory of such sets:

Suppose that for {leanRef}`α : Type u` we define the {leanRef}`Set `{leanRef (in := "(α : Type u)")}`α`{leanRef}` := α → Prop` to
denote the type of subsets of {leanRef (in := "(α : Type u)")}`α`, essentially identifying subsets
with predicates. By combining {leanRef}`funext` and {leanRef}`propext`, we obtain an
extensional theory of such sets:

```lean
def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

end Set
```

假设对于 {leanRef}`α : Type u`，我们定义 {leanRef}`Set `{leanRef (in := "(α : Type u)")}`α`{leanRef}` := α → Prop` 来表达 {leanRef (in := "(α : Type u)")}`α` 子集的类型，
本质上是用谓词来表示子集。通过组合 {leanRef}`funext` 和 {leanRef}`propext`，
我们得到了一个这样的集合的外延性理论：
:::

-- We can then proceed to define the empty set and set intersection, for
-- example, and prove set identities:

然后我们可以继续定义空集和集合交集，例如，并证明集合恒等式：

```lean
def Set (α : Type u) := α → Prop
namespace Set
def mem (x : α) (a : Set α) := a x
infix:50 (priority := high) "∈" => mem
theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))
------
def empty : Set α := fun _ => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun _ => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun _ => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun _ => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
-----
end Set
```

-- The following is an example of how function extensionality blocks
-- computation inside the Lean kernel:

以下是函数外延性如何阻碍 Lean 内核中计算的示例：

```lean
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

-- First, we show that the two functions {leanRef}`f` and {leanRef}`g` are equal using
-- function extensionality, and then we cast {leanRef}`0` of type {lean}`Nat` by
-- replacing {leanRef}`f` by {leanRef}`g` in the type. Of course, the cast is
-- vacuous, because {lean}`Nat` does not depend on {leanRef}`f`. But that is enough
-- to do the damage: under the computational rules of the system, we now
-- have a closed term of {lean}`Nat` that does not reduce to a numeral. In this
-- case, we may be tempted to reduce the expression to {lean}`0`. But in
-- nontrivial examples, eliminating cast changes the type of the term,
-- which might make an ambient expression type incorrect. The virtual
-- machine, however, has no trouble evaluating the expression to
-- {lean}`0`. Here is a similarly contrived example that shows how
-- {lean}`propext` can get in the way:

首先，我们使用函数外延性证明两个函数 {leanRef}`f` 和 {leanRef}`g` 相等，
然后我们通过在类型中将 {leanRef}`f` 替换为 {leanRef}`g` 来转换类型为 {lean}`Nat` 的 {leanRef}`0`。
当然，这种转换是空洞的，因为 {lean}`Nat` 不依赖于 {leanRef}`f`。但这足以造成破坏：
在系统的计算规则下，我们现在有一个 {lean}`Nat` 的封闭项，它不会归约为一个数值。
在这种情况下，我们可能会试图将表达式归约为 {lean}`0`。但在非平凡的例子中，
消除转换会改变项的类型，这可能会使周围的表达式类型不正确。
然而，虚拟机在将表达式求值为 {lean}`0` 方面没有任何问题。
这是一个类似的人为示例，展示了 {lean}`propext` 如何造成阻碍：

```lean
theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val
```

-- Current research programs, including work on _observational type
-- theory_ and _cubical type theory_, aim to extend type theory in ways
-- that permit reductions for casts involving function extensionality,
-- quotients, and more. But the solutions are not so clear-cut, and the
-- rules of Lean's underlying calculus do not sanction such reductions.

当前的研究项目，包括_观察类型论（Observational Type Theory）_和_立方类型论（Cubical Type Theory）_的工作，
旨在以允许涉及函数外延性、商等的转换进行归约的方式扩展类型论。
但解决方案并不那么明确，Lean 的底层演算规则也不支持这种归约。

-- In a sense, however, a cast does not change the meaning of an
-- expression. Rather, it is a mechanism to reason about the expression's
-- type. Given an appropriate semantics, it then makes sense to reduce
-- terms in ways that preserve their meaning, ignoring the intermediate
-- bookkeeping needed to make the reductions type-correct. In that case,
-- adding new axioms in {lean}`Prop` does not matter; by {tech}[proof irrelevance],
-- an expression in {lean}`Prop` carries no information, and can be safely
-- ignored by the reduction procedures.

然而，从某种意义上说，转换并不会改变表达式的含义。相反，它是一种推理表达式类型的机制。
给定适当的语义，以保留其含义的方式归约项是有意义的，忽略使归约类型正确所需的中间簿记。
在这种情况下，在 {lean}`Prop` 中添加新公理并不重要；通过{tech}[证明无关性]，
{lean}`Prop` 中的表达式不携带任何信息，并且可以被归约过程安全地忽略。

-- # Quotients
# 商
%%%
tag := "quotients"
%%%

:::setup
```
variable (α : Sort u) (r : α → α → Prop) (f : α → β) (x y : α) (f' : Quot r → β)
notation α " / " r:max => Quot (α := α) r
notation "⟦" x "⟧" => Quot.mk _ x

```
-- Let {lean}`α` be any type, and let {lean}`r` be an equivalence relation on
-- {lean}`α`. It is mathematically common to form the “quotient” {lean}`α / r`,
-- that is, the type of elements of {lean}`α` “modulo” {lean}`r`. Set
-- theoretically, one can view {lean}`α / r` as the set of equivalence
-- classes of {lean}`α` modulo {lean}`r`. If {lean}`f : α → β` is any function that
-- respects the equivalence relation in the sense that for every
-- {lean}`x y : α`, {lean}`r x y` implies {lean}`f x = f y`, then {lean}`f` “lifts” to a function
-- {lean}`f' : α / r → β` defined on each equivalence class {lean (type := "Quot r")}`⟦x⟧` by
-- {lean}`f' ⟦x⟧ = f x`. Lean's standard library extends the Calculus of
-- Constructions with additional constants that perform exactly these
-- constructions, and installs this last equation as a definitional
-- reduction rule.

设 {lean}`α` 为任意类型，且 {lean}`r` 为 {lean}`α` 上的等价关系。在数学中，
常见的做法是形成 *商（Quotient）* {lean}`α / r`，即 {lean}`α` 中元素的类型 _模（modulo）_ {lean}`r`。
从集合论的角度，可以将 {lean}`α / r` 视为 {lean}`α` 模 {lean}`r` 的等价类的集合。
若 {lean}`f : α → β` 是任意满足等价关系的函数，即对于任意 {lean}`x y : α`，{lean}`r x y`
蕴含 {lean}`f x = f y`，则 {lean}`f` _提升（lift）_ 到函数 {lean}`f' : α / r → β`，
其在每个等价类 {lean (type := "Quot r")}`⟦x⟧` 上由 {lean}`f' ⟦x⟧ = f x` 定义。
Lean 的标准库通过执行这些构造的附加常量来扩展构造演算，并将该最后的方程作为定义归约规则。

-- In its most basic form, the quotient construction does not even
-- require {lean}`r` to be an equivalence relation. The following constants
-- are built into Lean:

在最基本的表述形式中，商构造甚至不需要 {lean}`r` 成为一个等价关系。
下列常量被内置在 Lean 中：
:::

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β
------
end Hidden
```
:::setup
```
variable (α : Type u) (r : α → α → Prop) (a : α) (f : α → β) (h : ∀ a b, r a b → f a = f b)
```
-- The first one forms a type {lean}`Quot r` given a type {lean}`α` by any binary
-- relation {lean}`r` on {lean}`α`. The second maps {lean}`α` to {lit}`Quot α`, so that
-- if {lean}`r : α → α → Prop` and {lit}`a : α`, then {lean}`Quot.mk r a` is an
-- element of {lean}`Quot r`. The third principle, {lean}`Quot.ind`, says that
-- every element of {lean}`Quot.mk r a` is of this form.  As for
-- {lean}`Quot.lift`, given a function {lean}`f : α → β`, if {lean}`h` is a proof
-- that {lean}`f` respects the relation {lean}`r`, then {lean}`Quot.lift f h` is the
-- corresponding function on {lean}`Quot r`. The idea is that for each
-- element {lean}`a` in {lean}`α`, the function {lean}`Quot.lift f h` maps
-- {lean}`Quot.mk r a` (the {lean}`r`-class containing {lean}`a`) to {lean}`f a`, wherein {lean}`h`
-- shows that this function is well defined. In fact, the computation
-- principle is declared as a reduction rule, as the proof below makes
-- clear.

第一条公理根据任何二元关系 {lean}`r` 的类型 {lean}`α` 形成类型 {lean}`Quot r`。
第二条公理将 {lean}`α` 映射到 {lit}`Quot α`，因此若 {lean}`r : α → α → Prop` 且 {lit}`a : α`，
则 {lean}`Quot.mk r a` 是 {lean}`Quot r` 的一个元素。
第三条公理 {lean}`Quot.ind` 是说 {lean}`Quot.mk r a` 的每个元素都属于此形式。
至于 {lean}`Quot.lift`，给定函数 {lean}`f : α → β`，若 {lean}`h` 是一个“{lean}`f`
遵循关系 {lean}`r`”的证明，则 {lean}`Quot.lift f h` 是 {lean}`Quot r` 上的对应函数。
其思想是对于 {lean}`α` 中的每个元素 {lean}`a`，函数 {lean}`Quot.lift f h`
将 {lean}`Quot.mk r a`（包含 {lean}`a` 的 {lean}`r`-类）映射到 {lean}`f a`，
其中 {lean}`h` 表明此函数是良定义的。事实上，计算公理被声明为一个归约规则，
如下方的证明所示。


```lean
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- the quotient type
#check (Quot mod7Rel : Type)

-- the class of numbers equivalent to 4
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f a = f b := by
  simp [mod7Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : Quot mod7Rel → Bool)

-- the computation principle
example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7Rel a) = f a :=
  rfl
```


-- The four constants, {lean}`Quot`, {lean}`Quot.mk`, {lean}`Quot.ind`, and
-- {lean}`Quot.lift` in and of themselves are not very strong. You can check
-- that the {lean}`Quot.ind` is satisfied if we take {lean}`Quot r` to be simply
-- {lean}`α`, and take {lean}`Quot.lift` to be the identity function (ignoring
-- {lean}`h`). For that reason, these four constants are not viewed as
-- additional axioms.

四个常量 {lean}`Quot`、{lean}`Quot.mk`、{lean}`Quot.ind` 和 {lean}`Quot.lift` 在它们本身上并不强。
你可以检查如果我们把 {lean}`Quot r` 简单地取为 {lean}`α`，并取 {lean}`Quot.lift` 为恒等函数
（忽略 {lean}`h`），那么 {lean}`Quot.ind` 将得到满足。
由于这个原因，这四个常量并没有被看作附加公理。
:::

:::comment
```
<!--
    variables α β : Type
    variable  r : α → α → Prop
    variable  a : α
    variable  f : α → β
    variable   h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂
    theorem thm : quot.lift f h (quot.mk r a) = f a := rfl
    -- BEGIN
    #print axioms thm   -- no axioms
    -- END
-->
```

-- They are, like inductively defined types and the associated
-- constructors and recursors, viewed as part of the logical framework.

-- What makes the {lean}`Quot` construction into a bona fide quotient is the
-- following additional axiom:

和归纳定义的类型以及相关的构造子和递归器一样，它们也被视为逻辑框架的一部分。

使 {lean}`Quot` 构造成为真正商的是以下一个附加公理：
:::

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
universe u v
------
axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
```

-- This is the axiom that asserts that any two elements of {leanRef}`α` that are
-- related by {leanRef}`r` become identified in the quotient. If a theorem or
-- definition makes use of {leanRef}`Quot.sound`, it will show up in the
-- {kw}`#print axioms` command.

这条公理断言 {leanRef}`α` 的任何两个元素，只要满足关系 {leanRef}`r`，就能在商中被识别。
如果定理或定义使用了 {leanRef}`Quot.sound`，它将会在 {kw}`#print axioms` 命令中显示。

:::setup
```
variable (α : Type u) (r : α → α → Prop)  (r' r'': α → α → Prop) (a b : α)
```

-- Of course, the quotient construction is most commonly used in
-- situations when {lean}`r` is an equivalence relation. Given {lean}`r` as
-- above, if we define {lean}`r'` according to the rule {lean}`r' a b` iff
-- {lean}`Quot.mk r a = Quot.mk r b`, then it's clear that {lean}`r'` is an
-- equivalence relation. Indeed, {lean}`r'` is the _kernel_ of the function
-- {lean}`fun a => Quot.mk r a`.  The axiom {lean}`Quot.sound` says that {lean}`r a b`
-- implies {lean}`r' a b`. Using {lean}`Quot.lift` and {lean}`Quot.ind`, we can show
-- that {lean}`r'` is the smallest equivalence relation containing {lean}`r`, in
-- the sense that if {lean}`r''` is any equivalence relation containing
-- {lean}`r`, then {lean}`r' a b` implies {lean}`r'' a b`. In particular, if {lean}`r`
-- was an equivalence relation to start with, then for all {lean}`a` and
-- {lean}`b` we have {lean}`r a b` iff {lean}`r' a b`.

当然，当 {lean}`r` 是等价关系时，商集的结构是最常用的。给定上面的 {lean}`r`，
如果我们根据法则 {lean}`r' a b` 当且仅当 {lean}`Quot.mk r a = Quot.mk r b` 定义 {lean}`r'`，
那么显然 {lean}`r'` 就是一个等价关系。事实上，{lean}`r'` 是函数 {lean}`fun a => Quot.mk r a`
的 _核（Kernel）_ 。公理 {lean}`Quot.sound` 表明 {lean}`r a b` 蕴含 {lean}`r' a b`。
使用 {lean}`Quot.lift` 和 {lean}`Quot.ind`，我们可以证明 {lean}`r'` 是包含 {lean}`r` 的最小的等价关系，
意思就是，如果 {lean}`r''` 是包含 {lean}`r` 的任意等价关系，则 {lean}`r' a b` 蕴含 {lean}`r'' a b`。
特别地，如果 {lean}`r` 开始就是一个等价关系，那么对任意 {lean}`a` 和 {lean}`b`，我们都有
{lean}`r a b` 当且仅当 {lean}`r' a b`。
:::

-- To support this common use case, the standard library defines the
-- notion of a _setoid_, which is simply a type with an associated
-- equivalence relation:

为支持这种通用使用案例，标准库定义了 _广集（Setoid）_ 的概念，
它只是一个带有与之关联的等价关系的类型：

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid
------
end Hidden
```

-- Given a type {leanRef (in := "Setoid (α")}`α`, a relation {leanRef (in := "Equivalence r")}`r`
-- on {leanRef (in := "Setoid (α")}`α`, and a proof {leanRef}`iseqv`
-- that {leanRef (in := "Equivalence r")}`r` is an equivalence relation, we can define an
-- instance of the {leanRef (in := "class Setoid")}`Setoid` class.

给定一个类型 {leanRef (in := "Setoid (α")}`α`，其上的关系 {leanRef (in := "Equivalence r")}`r`，
以及一个证明 {leanRef}`iseqv` 证明 {leanRef (in := "Equivalence r")}`r` 是一个等价关系，
我们可以定义 {leanRef (in := "class Setoid")}`Setoid` 类的一个实例。

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r
------
end Hidden
```

:::setup
```
variable (α : Type u) [Setoid α] (a b : α)
```


-- The constants {lean}`Quotient.mk`, {lean}`Quotient.ind`, {lean}`Quotient.lift`,
-- and {lean}`Quotient.sound` are nothing more than the specializations of
-- the corresponding elements of {lean}`Quot`. The fact that type class
-- inference can find the setoid associated to a type {lean}`α` brings a
-- number of benefits. First, we can use the notation {lean}`a ≈ b` (entered
-- with {kbd}`\approx`) for {lean}`Setoid.r a b`, where the instance of
-- {lean}`Setoid` is implicit in the notation {lean}`Setoid.r`. We can use the
-- generic theorems {lean}`Setoid.refl`, {lean}`Setoid.symm`, {lean}`Setoid.trans` to
-- reason about the relation. Specifically with quotients we can use the
-- theorem {lean}`Quotient.exact`:

常量 {lean}`Quotient.mk`、{lean}`Quotient.ind`、{lean}`Quotient.lift`
以及 {lean}`Quotient.sound` 仅为 {lean}`Quot` 对应元素的特化形式。
类型类推断能找到与类型 {lean}`α` 关联的广集，这带来了大量好处。
首先，我们可以对 {lean}`Setoid.r a b` 使用符号 {lean}`a ≈ b`（用 {kbd}`\approx` 输入），
其中 {lean}`Setoid` 的实例在符号 {lean}`Setoid.r` 中是内隐的。
我们可以使用通用定理 {lean}`Setoid.refl`、{lean}`Setoid.symm`、{lean}`Setoid.trans`
来推断关系。具体来说，在商中，我们可以使用定理 {lean}`Quotient.exact`：

```signature
Quotient.exact {α : Sort u} {s : Setoid α} {a b : α} :
  Quotient.mk s a = Quotient.mk s b →
  a ≈ b
```

-- Together with {lean}`Quotient.sound`, this implies that the elements of
-- the quotient correspond exactly to the equivalence classes of elements
-- in {lean}`α`.

结合 {lean}`Quotient.sound`，这意味着商的各个元素精确对应于 {lean}`α` 中各元素的等价类。
:::

:::setup
```
variable (α : Type u) (β : Type v)
```

-- Recall that in the standard library, {lean}`α × β` represents the
-- Cartesian product of the types {lean}`α` and {lean}`β`. To illustrate the use
-- of quotients, let us define the type of _unordered_ pairs of elements
-- of a type {lean}`α` as a quotient of the type {lean}`α × α`. First, we define
-- the relevant equivalence relation:

回顾一下标准库中的 {lean}`α × β` 代表类型 {lean}`α` 和 {lean}`β` 的笛卡尔积。
为了说明商的用法，让我们将类型为 {lean}`α` 的元素构成的 _无序对（Unordered Pair）_ 的类型定义为
{lean}`α × α` 类型的商。首先，我们定义相关的等价关系：
:::
```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv
```

-- The next step is to prove that {leanRef}`eqv` is in fact an equivalence
-- relation, which is to say, it is reflexive, symmetric and
-- transitive. We can prove these three facts in a convenient and
-- readable way by using dependent pattern matching to perform
-- case-analysis and break the hypotheses into pieces that are then
-- reassembled to produce the conclusion.

下一步是证明 {leanRef}`eqv` 实际上是一个等价关系，即满足自反性、对称性和传递性。
我们可以使用依值模式匹配进行情况分析，将假设分解然后重新组合以得出结论，
从而以一种简便易读的方式证明这三个事实。

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
------
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)

private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)

private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
```

:::leanFirst
-- Now that we have proved that {leanRef}`eqv` is an equivalence relation, we
-- can construct a {leanRef}`Setoid (α × α)`, and use it to define the type
-- {leanRef}`UProd α` of unordered pairs.

现在我们已经证明了 {leanRef}`eqv` 是一个等价关系，我们可以构造一个 {leanRef}`Setoid (α × α)`，
并使用它来定义无序对的类型 {leanRef}`UProd α`。

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
------
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)

notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd
```
:::

:::setup
```
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)


notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

end UProd

variable (a₁ a₂ : α)
```

-- Notice that we locally define the notation {lean}`{a₁, a₂}` for unordered
-- pairs as {lean}`Quotient.mk' (a₁, a₂)`. This is useful for illustrative
-- purposes, but it is not a good idea in general, since the notation
-- will shadow other uses of curly brackets, such as for records and
-- sets.
--
-- We can easily prove that {lean}`{a₁, a₂} = {a₂, a₁}` using {lean}`Quot.sound`,
-- since we have {lean}`(a₁, a₂) ~ (a₂, a₁)`.

注意，我们局部地将无序对的符号 {lean}`{a₁, a₂}` 定义为 {lean}`Quotient.mk' (a₁, a₂)`。
这对于演示目的很有用，但通常不是一个好主意，因为该符号会遮蔽花括号的其他用途，
例如用于记录和集合。

我们可以使用 {lean}`Quot.sound` 轻松证明 {lean}`{a₁, a₂} = {a₂, a₁}`，
因为我们有 {lean}`(a₁, a₂) ~ (a₂, a₁)`。
:::

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence
def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)
namespace UProd
def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)
notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
------
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
------
end UProd
```

:::leanFirst
-- To complete the example, given {leanRef}`a : α` and {leanRef}`u : UProd α`, we
-- define the proposition {leanRef (in := "mem (a : α) (u : UProd α)")}`a`{lit}`  ∈  `{leanRef (in := "mem (a : α) (u : UProd α)")}`u` which should hold if {leanRef (in := "mem (a : α) (u : UProd α)")}`a` is one of
-- the elements of the unordered pair {leanRef (in := "mem (a : α) (u : UProd α)")}`u`. First, we define a similar
-- proposition {leanRef}`mem_fn`{leanRef (in := "mem (a : α) (u : UProd α)")}` a`{leanRef (in := "mem (a : α) (u : UProd α)")}` u` on (ordered) pairs; then we show that
-- {leanRef}`mem_fn` respects the equivalence relation {leanRef}`eqv` with the lemma
-- {leanRef}`mem_respects`. This is an idiom that is used extensively in the
-- Lean standard library.

为了完成这个例子，给定 {leanRef}`a : α` 和 {leanRef}`u : UProd α`，
我们定义命题 {leanRef (in := "mem (a : α) (u : UProd α)")}`a`{lit}`  ∈  `{leanRef (in := "mem (a : α) (u : UProd α)")}`u`，如果 {leanRef (in := "mem (a : α) (u : UProd α)")}`a` 是无序对 {leanRef (in := "mem (a : α) (u : UProd α)")}`u`
的元素之一，则该命题成立。首先，我们在（有序）对上定义一个类似的命题
{leanRef}`mem_fn`{leanRef (in := "mem (a : α) (u : UProd α)")}` a`{leanRef (in := "mem (a : α) (u : UProd α)")}` u`；然后我们用引理 {leanRef}`mem_respects`
证明 {leanRef}`mem_fn` 遵循等价关系 {leanRef}`eqv`。
这是 Lean 标准库中广泛使用的一种惯用语。

```lean
set_option linter.unusedVariables false
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv
private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩
private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)
private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)
private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence
def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)
namespace UProd
def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)
notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
------
private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

-- auxiliary lemma for proving mem_respects
private theorem mem_swap {a : α} :
      ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) => by
    apply propext
    apply Iff.intro
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h

private theorem mem_respects : {p₁ p₂ : α × α} → (a : α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by
    simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by
    simp_all only
    apply mem_swap

def mem (a : α) (u : UProd α) : Prop :=
  Quot.liftOn u (fun p => mem_fn a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 (priority := high) " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
  fun h => h
---------
end UProd
```
:::

-- For convenience, the standard library also defines {lean}`Quotient.lift₂`
-- for lifting binary functions, and {lit}`Quotient.ind₂` for induction on
-- two variables.

为了方便起见，标准库还定义了用于提升二元函数的 {lean}`Quotient.lift₂`，
以及用于两个变量归纳的 {lit}`Quotient.ind₂`。
:::setup
```
variable (α : Sort u) (β : α → Sort v) (f₁ f₂ f : (x : α) → β x) (a : α)

def extfun (α : Sort u) (β : α → Sort v) := Quot (fun (f g : (x : α) → β x) => ∀ x, f x = g x)

def extfun_app {α β} : extfun α β → (x : α) → β x := fun f x =>
  Quot.lift (· x) (by intros; simp [*]) f

```

-- We close this section with some hints as to why the quotient
-- construction implies function extensionality. It is not hard to show
-- that extensional equality on the {lean}`(x : α) → β x` is an equivalence
-- relation, and so we can consider the type {lean}`extfun α β` of functions
-- “up to equivalence.” Of course, application respects that equivalence
-- in the sense that if {lean}`f₁` is equivalent to {lean}`f₂`, then {lean}`f₁ a` is
-- equal to {lean}`f₂ a`. Thus application gives rise to a function
-- {lean}`extfun_app : extfun α β → (x : α) → β x`. But for every {lean}`f`,
-- {lean}`extfun_app (.mk _ f)` is definitionally equal to {lean}`fun x => f x`, which is
-- in turn definitionally equal to {lean}`f`. So, when {lean}`f₁` and {lean}`f₂` are
-- extensionally equal, we have the following chain of equalities:

我们在本节的最后给出一些提示，说明为什么商构造蕴含函数外延性。
不难证明 {lean}`(x : α) → β x` 上的外延相等是一个等价关系，
因此我们可以考虑“在等价意义下”的函数类型 {lean}`extfun α β`。
当然，应用（Application）遵循该等价关系，即如果 {lean}`f₁` 等价于 {lean}`f₂`，
则 {lean}`f₁ a` 等于 {lean}`f₂ a`。因此，应用产生了一个函数
{lean}`extfun_app : extfun α β → (x : α) → β x`。但是对于每个 {lean}`f`，
{lean}`extfun_app (.mk _ f)` 在定义上等于 {lean}`fun x => f x`，
而后者在定义上又等于 {lean}`f`。因此，当 {lean}`f₁` 和 {lean}`f₂` 外延相等时，
我们有以下等式链：

```lean
variable {α : Sort u} {β : α → Sort v}

def extfun (α : Sort u) (β : α → Sort v) := Quot (fun (f g : (x : α) → β x) => ∀ x, f x = g x)

def extfun_app {α β} (f : extfun α β) (x : α) : β x :=
  Quot.lift (· x) (by intros; simp [*]) f
----------
example (f₁ f₂ : (x : α) → β x) (h : ∀ x, f₁ x = f₂ x) :=
  calc f₁
    _ = extfun_app (.mk _ f₁) := rfl
    _ = extfun_app (.mk _ f₂) := by rw [Quot.sound]; trivial
    _ = f₂ := rfl

```

-- As a result, {leanRef}`f₁` is equal to {leanRef}`f₂`.

结果是，{leanRef}`f₁` 等于 {leanRef}`f₂`。
:::

-- # Choice
# 选择公理
%%%
tag := "choice"
%%%

:::leanFirst
-- To state the final axiom defined in the standard library, we need the
-- {leanRef}`Nonempty` type, which is defined as follows:

为了陈述标准库中定义的最后一个公理，我们需要 {leanRef}`Nonempty` 类型，它的定义如下：

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
------
class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α
------
end Hidden
```
:::

:::setup
```
variable {α : Sort u}
```

-- Because {lean}`Nonempty α` has type {lean}`Prop` and its constructor contains data, it can only eliminate to {lean}`Prop`.
-- In fact, {lean}`Nonempty α` is equivalent to {lean}`∃ x : α, True`:

由于 {lean}`Nonempty α` 的类型为 {lean}`Prop`，其构造子包含数据，所以只能消去到 {lean}`Prop`。
事实上，{lean}`Nonempty α` 等价于 {lean}`∃ x : α, True`：
:::

```lean
example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro (fun ⟨a⟩ => ⟨a, trivial⟩) (fun ⟨a, h⟩ => ⟨a⟩)
```

-- Our axiom of choice is now expressed simply as follows:

我们的选择公理现在可以简单地表示如下：

```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
universe u
------
axiom choice {α : Sort u} : Nonempty α → α
------
end Hidden
```

:::setup
```
variable {α : Sort u} {h : Nonempty α}
open Classical
```

-- Given only the assertion {lean}`h` that {lean}`α` is nonempty, {lean}`choice h`
-- magically produces an element of {lean}`α`. Of course, this blocks any
-- meaningful computation: by the interpretation of {lean}`Prop`, {lean}`h`
-- contains no information at all as to how to find such an element.

给定唯一断言 {lean}`h`，即 {lean}`α` 非空，{lean}`choice h` 神奇地产生了一个 {lean}`α` 的元素。
当然，这阻碍了任何有意义的计算：根据 {lean}`Prop` 的解释，{lean}`h` 根本不包含任何信息，
因而无法找到这样的元素。

:::

-- This is found in the {lit}`Classical` namespace, so the full name of the
-- theorem is {lean}`Classical.choice`. The choice principle is equivalent to
-- the principle of *indefinite description*, which can be expressed with
-- subtypes as follows:

这可以在 {lit}`Classical` 命名空间中找到，所以定理的全名是 {lean}`Classical.choice`。
选择公理等价于_非限定摹状词（Indefinite Description）_原理，可通过子类型表示如下：

```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
namespace Hidden
universe u
axiom choice {α : Sort u} : Nonempty α → α
------
noncomputable def indefiniteDescription {α : Sort u}
    (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩
------
end Hidden
```

:::setup
```
variable {α : Sort u} {h : Nonempty α}
open Classical
```
-- Because it depends on {lean}`choice`, Lean cannot generate executable code for
-- {lean}`indefiniteDescription`, and so requires us to mark the definition
-- as {kw}`noncomputable`. Also in the {lit}`Classical` namespace, the
-- function {lean}`choose` and the property {lean}`choose_spec` decompose the two
-- parts of the output of {lean}`indefiniteDescription`:

因为依赖于 {lean}`choice`，Lean 不能为 {lean}`indefiniteDescription` 生成可执行代码，
所以要求我们将定义标记为 {kw}`noncomputable`。同样在 {lit}`Classical` 命名空间中，
函数 {lean}`choose` 和属性 {lean}`choose_spec` 分离了 {lean}`indefiniteDescription` 输出的两个部分：



```lean  (suppressNamespaces := "Hidden") (allowVisible := false)
open Classical
namespace Hidden
------
variable {α : Sort u} {p : α → Prop}

noncomputable def choose (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
------
end Hidden
```

-- The {lean}`choice` principle also erases the distinction between the
-- property of being {lean}`Nonempty` and the more constructive property of
-- being {lean}`Inhabited`:

{lean}`choice` 选择公理也消除了 {lean}`Nonempty` 特性与更加具有构造性的
{lean}`Inhabited` 特性之间的区别。

```lean
open Classical
------
noncomputable def inhabited_of_nonempty (h : Nonempty α) : Inhabited α :=
  choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)
```
:::

-- In the next section, we will see that {lean}`propext`, {lean}`funext`, and
-- {leanRef}`choice`, taken together, imply the law of the excluded middle and
-- the decidability of all propositions. Using those, one can strengthen
-- the principle of indefinite description as follows:

在下一节中，我们将会看到 {lean}`propext`、{lean}`funext` 和 {leanRef}`choice`，
合起来就构成了排中律以及所有命题的可判定性。使用它们，我们可以加强如下非限定摹状词原理：

::::setup
```
open Classical
```

```signature
strongIndefiniteDescription {α : Sort u} (p : α → Prop)
  (h : Nonempty α) :
  {x // (∃ (y : α), p y) → p x}
```


-- Assuming the ambient type {leanRef}`α` is nonempty,
-- {leanRef}`strongIndefiniteDescription`{lit}` `{leanRef}`p` produces an element of {leanRef}`α`
-- satisfying {leanRef}`p` if there is one. The data component of this
-- definition is conventionally known as *Hilbert's epsilon function*:

假设环境类型 {leanRef}`α` 非空，{leanRef}`strongIndefiniteDescription`{lit}` `{leanRef}`p` 产生一个满足 {leanRef}`p`
的元素 {leanRef}`α`（如果存在的话）。该定义的数据部分通常被称为 _希尔伯特 ε 函数_：

```signature
epsilon {α : Sort u} [h : Nonempty α] (p : α → Prop) : α
```

```signature
epsilon_spec {α : Sort u} {p : α → Prop}
  (hex : ∃ (y : α), p y) :
  p (@epsilon _ (nonempty_of_exists hex) p)
```


::::

-- # The Law of the Excluded Middle
# 排中律
%%%
tag := "the-law-of-the-excluded-middle"
%%%

-- The law of the excluded middle is the following:

排中律如下所示：

```signature
Classical.em : ∀ (p : Prop), p ∨ ¬p
```


-- [Diaconescu's theorem](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem) states
-- that the axiom of choice is sufficient to derive the law of excluded
-- middle. More precisely, it shows that the law of the excluded middle
-- follows from {lean}`Classical.choice`, {lean}`propext`, and {lean}`funext`. We
-- sketch the proof that is found in the standard library.

[迪亚科内斯库定理](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem) 表明
选择公理足以导出排中律。更确切地说，它表明排中律源自于 {lean}`Classical.choice`，
{lean}`propext` 和 {lean}`funext`。我们概述了标准库中的证明。

```save emProof
-- ANCHOR: emSetup
open Classical
theorem em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  -- ^ PROOF_STATE: em1
-- ANCHOR_END: emSetup
-- ANCHOR: emChoose
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
  -- ^ PROOF_STATE: em2
-- ANCHOR_END: emChoose
-- ANCHOR: emCases
  have not_uv_or_p : u ≠ v ∨ p := by
    match u_def, v_def with
    | Or.inr h, _ => exact Or.inr h
    | _, Or.inr h => exact Or.inr h
    | Or.inl hut, Or.inl hvf =>
      apply Or.inl
      simp [hvf, hut, true_ne_false]
-- ANCHOR_END: emCases
-- ANCHOR: emNext
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
-- ANCHOR_END: emNext
-- ANCHOR: emDone
  match not_uv_or_p with
  | Or.inl hne =>
    exact Or.inr (mt p_implies_uv hne)
  | Or.inr h   =>
    exact Or.inl h
-- ANCHOR_END: emDone
```

:::leanFirst
-- First, we import the necessary axioms, and define two predicates {leanRef}`U` and {leanRef}`V`:

首先，我们导入必要的公理，并定义两个谓词 {leanRef}`U` 和 {leanRef}`V`：

```savedAnchor emSetup
open Classical
theorem em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
```

:::

-- If {leanRef}`p` is true, then every element of {lean}`Prop` is in both {leanRef}`U` and {leanRef}`V`.
-- If {leanRef}`p` is false, then {leanRef}`U` is the singleton {leanRef}`True`, and {leanRef}`V` is the singleton {leanRef}`False`.

当 {leanRef}`p` 为真时，{lean}`Prop` 的所有元素既在 {leanRef}`U` 中又在 {leanRef}`V` 中。
当 {leanRef}`p` 为假时，{leanRef}`U` 是单元素的 {leanRef}`True`，{leanRef}`V` 是单元素的 {leanRef}`False`。

:::leanFirst
-- Next, we use {leanRef}`choose` to choose an element from each of {leanRef}`U` and {leanRef}`V`:

接下来，我们使用 {leanRef}`choose` 从 {leanRef}`U` 和 {leanRef}`V` 中各选取一个元素：

```savedAnchor emChoose
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
```
:::

:::leanFirst
-- Each of {leanRef}`U` and {leanRef}`V` is a disjunction, so {leanRef}`u_def` and {leanRef}`v_def`
-- represent four cases. In one of these cases, {leanRef}`u = True` and
-- {leanRef}`v = False`, and in all the other cases, {leanRef}`p` is true. Thus we have:

{leanRef}`U` 和 {leanRef}`V` 都是析取，所以 {leanRef}`u_def` 和 {leanRef}`v_def` 表示四种情况。
在其中一种情况下，{leanRef}`u = True` 且 {leanRef}`v = False`，在所有其他情况下，
{leanRef}`p` 为真。因此我们有：

```savedAnchor emCases
  have not_uv_or_p : u ≠ v ∨ p := by
    match u_def, v_def with
    | Or.inr h, _ => exact Or.inr h
    | _, Or.inr h => exact Or.inr h
    | Or.inl hut, Or.inl hvf =>
      apply Or.inl
      simp [hvf, hut, true_ne_false]
```
:::

-- On the other hand, if {leanRef}`p` is true, then, by function extensionality
-- and propositional extensionality, {leanRef}`U` and {leanRef}`V` are equal. By the
-- definition of {leanRef}`u` and {leanRef}`v`, this implies that they are equal as well.

另一方面，若 {leanRef}`p` 为真，则由函数的外延性和命题的外延性，可得 {leanRef}`U` 和 {leanRef}`V` 相等。
根据 {leanRef}`u` 和 {leanRef}`v` 的定义，这蕴含了它们也相等。

```savedAnchor emNext
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; rfl
    show u = v from h₀ _ _
```


-- Putting these last two facts together yields the desired conclusion:

将最后两个事实放在一起可以得出期望的结论：

```savedAnchor emDone
  match not_uv_or_p with
  | Or.inl hne =>
    exact Or.inr (mt p_implies_uv hne)
  | Or.inr h   =>
    exact Or.inl h
```


-- Consequences of excluded middle include double-negation elimination,
-- proof by cases, and proof by contradiction, all of which are described
-- in the section on {ref "classical-logic"}[classical logic].
-- The law of the excluded middle and propositional extensionality imply propositional completeness:

排除中律的推论包括双重否定消除、分情况证明和反证法，
所有这些都在{ref "classical-logic"}[经典逻辑一节]中描述。
排除中律和命题外延性律蕴含了命题完备性：

```lean (suppressNamespaces := "Hidden") (allowVisible := false)
open Classical
theorem propComplete (a : Prop) : a = True ∨ a = False :=
  match em a with
  | Or.inl ha =>
    Or.inl (propext (Iff.intro (fun _ => True.intro) (fun _ => ha)))
  | Or.inr hn =>
    Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))
```

-- Together with choice, we also get the stronger principle that every
-- proposition is decidable. Recall that the class of {lean}`Decidable`
-- propositions is defined as follows:

有了选择公理，我们也能得到一个更强的原则，即每个命题都是可判定的。
回想一下 {lean}`Decidable` 可判定性命题集定义如下：

```lean
namespace Hidden
------
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
------
end Hidden
```

::::setup
```
variable {p : Prop} {f : α → β} {c : Prop} [Decidable c] {t e : α}
open Classical (choose propDecidable)
```
:::leanFirst
-- In contrast to {lean}`p ∨ ¬ p`, which can only eliminate to {lean}`Prop`, the
-- type {lean}`Decidable p` is equivalent to the sum type {lit}`Sum p (¬ p)`, which
-- can eliminate to any type. It is this data that is needed to write an
-- if-then-else expression.

与 {lean}`p ∨ ¬ p` 不同，它只能消去到 {lean}`Prop`，类型 {lean}`Decidable p` 等效于和类型
{lit}`Sum p (¬ p)`，它可以消除至任何类型。
这就是编写“if-then-else（若-则-否则）”表达式所需的数据。

-- As an example of classical reasoning, we use {lean}`choose` to show that if
-- {lean}`f : α → β` is injective and {lean}`α` is inhabited, then {lean}`f` has a
-- left inverse. To define the left inverse {leanRef}`linv`, we use a dependent
-- if-then-else expression. Recall that {lean}`if h : c then t else e` is
-- notation for {lean}`dite c (fun h : c => t) (fun h : ¬ c => e)`. In the definition
-- of {leanRef}`linv`, choice is used twice: first, to show that
-- {leanRef}`(∃ a : α, f a = b)` is “decidable,” and then to choose an {leanRef}`a` such that
-- {leanRef}`f a = b`. Notice that {lean}`propDecidable` is a scoped instance and is activated
-- by the {leanRef}`open Classical` command. We use this instance to justify
-- the {kw}`if`-{kw}`then`-{kw}`else` expression. (See also the discussion in
-- {ref "decidable-propositions"}[Decidable Propositions]).

作为经典推理的一个示例，我们使用 {lean}`choose` 来证明，若 {lean}`f : α → β` 是单射的，
且 {lean}`α` 是可居的，则 {lean}`f` 是左逆的。为了定义左逆 {leanRef}`linv`，我们使用一个依值的
if-then-else 表达式。回忆一下，{lean}`if h : c then t else e` 是
{lean}`dite c (fun h : c => t) (fun h : ¬ c => e)` 的记法。在 {leanRef}`linv` 的定义中，
选择公理使用了两次：首先，为了证明 {leanRef}`(∃ a : α, f a = b)` 是“可判定的”，
需要选择一个 {leanRef}`a`，使得 {leanRef}`f a = b`。请注意，{lean}`propDecidable` 是一个作用域实例，
它通过 {leanRef}`open Classical` 命令激活。我们使用此实例来证明 {kw}`if`-{kw}`then`-{kw}`else` 表达式。
（还可以参阅 {ref "decidable-propositions"}[可判命题一节] 中的讨论）。


```lean
open Classical

noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b : β => if ex : (∃ a : α, f a = b) then choose ex else default

theorem linv_comp_self {f : α → β} [Inhabited α]
                       (inj : ∀ {a b}, f a = f b → a = b)
                       : linv f ∘ f = id :=
  funext fun a =>
    have ex  : ∃ a₁ : α, f a₁ = f a := ⟨a, rfl⟩
    have feq : f (choose ex) = f a  := choose_spec ex
    calc linv f (f a)
      _ = choose ex := rfl
      _ = a         := inj feq
```

-- From a classical point of view, {leanRef}`linv` is a function. From a
-- constructive point of view, it is unacceptable; because there is no
-- way to implement such a function in general, the construction is not
-- informative.

从经典逻辑的视角来看，{leanRef}`linv` 是一个函数。而从构造性视角来看，
它是不可接受的；由于没有实现这样一种函数的通用方法，因此该构造不具备信息量。
:::
::::
