<!--
Axioms and Computation
======================
-->

公理与计算
======================

<!--
We have seen that the version of the Calculus of Constructions that
has been implemented in Lean includes dependent function types,
inductive types, and a hierarchy of universes that starts with an
impredicative, proof-irrelevant ``Prop`` at the bottom. In this
chapter, we consider ways of extending the CIC with additional axioms
and rules. Extending a foundational system in such a way is often
convenient; it can make it possible to prove more theorems, as well as
make it easier to prove theorems that could have been proved
otherwise. But there can be negative consequences of adding additional
axioms, consequences which may go beyond concerns about their
correctness. In particular, the use of axioms bears on the
computational content of definitions and theorems, in ways we will
explore here.
-->

我们已经看到 Lean 中实现的构造演算的版本包括有：依值函数类型、
归纳类型以及一个以非直谓的与证明无关（Proof-Irrelevant）的 ``Prop`` 为底层的宇宙层级。
在本章中，我们要探讨使用附加公理和规则扩展 CIC 的方法。
用这种方式扩展一个基础系统通常很方便；它可以使得证明更多的定理成为可能，
并使得证明原本可以被证明的定理变得更容易。但是，添加附加公理可能会产生负面后果，
这些后果可能超出了人们对它们的正确性的担忧。
特别是，公理的使用会以我们将在本文中探究的方式，对定义和定理的计算内容产生影响。

<!--
Lean is designed to support both computational and classical
reasoning. Users that are so inclined can stick to a "computationally
pure" fragment, which guarantees that closed expressions in the system
evaluate to canonical normal forms. In particular, any closed
computationally pure expression of type ``Nat``, for example, will
reduce to a numeral.
-->

Lean 被设计为支持计算推理和经典推理。有此需求的用户可坚持使用「计算上纯粹」的片段，
它可以确保系统中的封闭表达式会求值为标准范式。具体说来，任何类型为 ``Nat``
的封闭计算上纯粹表达式最终都将归约为一个数值。

<!--
Lean's standard library defines an additional axiom, propositional
extensionality, and a quotient construction which in turn implies the
principle of function extensionality. These extensions are used, for
example, to develop theories of sets and finite sets. We will see
below that using these theorems can block evaluation in Lean's kernel,
so that closed terms of type ``Nat`` no longer evaluate to numerals. But
Lean erases types and propositional information when compiling
definitions to bytecode for its virtual machine evaluator, and since
these axioms only add new propositions, they are compatible with that
computational interpretation. Even computationally inclined users may
wish to use the classical law of the excluded middle to reason about
computation. This also blocks evaluation in the kernel, but it is
compatible with compilation to bytecode.
-->

Lean 的标准库定义了一个公理： **命题外延性（Propositional Extensionality）** 。
以及一个 **商（Qoutient）** 结构，它蕴含了函数外延性的公理。
这些扩展被用来发展如集合与有限集这些理论。我们在后面会看到，
这些定理的使用会阻碍 Lean 内核中的求值，因此 ``Nat`` 类型的封闭项不再求值为数值。
但是 Lean 在对其虚拟机器求值器进行字节码编译时会擦除类型和命题信息，
并且由于这些公理只增加了新的命题，它们与这种计算解释是相容的。
即使是倾向于可计算性的用户也可能希望使用排中律来推理计算。
这也会阻碍内核中的求值，但它与字节码编译是兼容的。

<!--
The standard library also defines a choice principle that is entirely
antithetical to a computational interpretation, since it magically
produces "data" from a proposition asserting its existence. Its use is
essential to some classical constructions, and users can import it
when needed. But expressions that use this construction to produce
data do not have computational content, and in Lean we are required to
mark such definitions as ``noncomputable`` to flag that fact.
-->

标准函数库还定义了一个选择公理（Choice Principle），该公理与计算诠释完全相反，
因为它神奇地根据断言自身存在的命题产生「数据」。
它对于一些经典结构来说是必不可少的，用户可以在需要时导入它。
但使用此构造来产生数据的表达式将不存在计算内容，
在 Lean 中我们需要将此类定义标记为 ``noncomputable``（不可计算的）以表明该事实。

<!--
Using a clever trick (known as Diaconescu's theorem), one can use
propositional extensionality, function extensionality, and choice to
derive the law of the excluded middle. As noted above, however, use of
the law of the excluded middle is still compatible with bytecode
compilation and code extraction, as are other classical principles, as
long as they are not used to manufacture data.
-->

使用一个巧妙的技巧（称为狄阿科涅斯库定理），人们可以使用命题外延性、
函数外延性和选择公理来导出排中律。然而，如上所述，使用排中律仍然兼容字节码编译和代码提取，
就像其他经典公理一样，只要它们不被用来制造数据。

<!--
To summarize, then, on top of the underlying framework of universes,
dependent function types, and inductive types, the standard library
adds three additional components:

- the axiom of propositional extensionality
- a quotient construction, which implies function extensionality
- a choice principle, which produces data from an existential proposition.
-->

总而言之，在我们的宇宙类型，依值函数类型和归纳类型的底层框架之上，
标准库增加了三个附加元素：

- 命题外延性公理
- 蕴含了函数外延性的的商构造
- 选择公理，它从存在命题中产生数据。

<!--
The first two of these block normalization within Lean, but are
compatible with bytecode evaluation, whereas the third is not amenable
to computational interpretation. We will spell out the details more
precisely below.
-->

前两项在 Lean 中对这些块标准化，但与字节码求值兼容，
而第三项不适合可计算性解释。我们将在下面更精确地说明这些细节。

<!--
Historical and Philosophical Context
------------------------------------
-->

历史与哲学背景
------------------------------------

<!--
For most of its history, mathematics was essentially computational:
geometry dealt with constructions of geometric objects, algebra was
concerned with algorithmic solutions to systems of equations, and
analysis provided means to compute the future behavior of systems
evolving over time. From the proof of a theorem to the effect that
"for every ``x``, there is a ``y`` such that ...", it was generally
straightforward to extract an algorithm to compute such a ``y`` given
``x``.
-->

历史上大部分时候，数学主要是计算性的：几何处理涉及几何对象的构造，
代数涉及方程组的算法解，分析提供了计算系统随时间演变的未来行为的方法。
从定理的证明到「对于每个 ``x``，都有一个 ``y`` 使得 ...」这一效果，
通常可以提取一种算法来根据给定的 ``x`` 计算这样的的 ``y``。

<!--
In the nineteenth century, however, increases in the complexity of
mathematical arguments pushed mathematicians to develop new styles of
reasoning that suppress algorithmic information and invoke
descriptions of mathematical objects that abstract away the details of
how those objects are represented. The goal was to obtain a powerful
"conceptual" understanding without getting bogged down in
computational details, but this had the effect of admitting
mathematical theorems that are simply *false* on a direct
computational reading.
-->

然而在 19 世纪，数学论证复杂性的提升推动了数学家发展新的推理风格，
抑制算法信息并调用数学对象，从而抽象掉了对象被表征的细节。
目标是在不陷入繁重的计算细节的情况下获得强大的「概念」理解，
但这可能导致数学定理在直接计算的解读上干脆就是  **错误**  的。

<!--
There is still fairly uniform agreement today that computation is
important to mathematics. But there are different views as to how best
to address computational concerns. From a *constructive* point of
view, it is a mistake to separate mathematics from its computational
roots; every meaningful mathematical theorem should have a direct
computational interpretation. From a *classical* point of view, it is
more fruitful to maintain a separation of concerns: we can use one
language and body of methods to write computer programs, while
maintaining the freedom to use nonconstructive theories and methods
to reason about them. Lean is designed to support both of these
approaches. Core parts of the library are developed constructively,
but the system also provides support for carrying out classical
mathematical reasoning.
-->

今天数学界仍在相当普遍地同意计算对于数学很重要。
但对于如何以最佳方式解决计算问题有不同的看法。
从 **构造性** 的角度来看，将数学与其计算根源分开是一个错误；
每条有意义的数学定理都应具有直接的计算解释。
从 **经典的** 角度来看，保持关注点的分离更有成效：
我们可以使用一种语言和方法体系编写计算机程序，
同时保持使用非构造性理论和方法对其进行推理的自由。
Lean 旨在支持这两种方法。库的核心部分以构造性方式开发，
但该系统还提供了支持进行经典数学推理的支持。

<!--
Computationally, the purest part of dependent type theory avoids the
use of ``Prop`` entirely. Inductive types and dependent function types
can be viewed as data types, and terms of these types can be
"evaluated" by applying reduction rules until no more rules can be
applied. In principle, any closed term (that is, term with no free
variables) of type ``Nat`` should evaluate to a numeral, ``succ
(... (succ zero)...)``.
-->

从计算的角度来看，依值类型论中最纯粹的部分完全避免使用 ``Prop``。
归纳类型和依值函数类型可以看作是数据类型，这些类型的项可以通过应用归约规则进行「求值」，
直到不能再应用任何规则为止。原则上，类型为 ``Nat`` 的任何封闭项（即没有自由变量的项）
都应求值为一个数值：``succ(... (succ zero)...)``。

<!--
Introducing a proof-irrelevant ``Prop`` and marking theorems
irreducible represents a first step towards separation of
concerns. The intention is that elements of a type ``p : Prop`` should
play no role in computation, and so the particular construction of a
term ``t : p`` is "irrelevant" in that sense. One can still define
computational objects that incorporate elements of type ``Prop``; the
point is that these elements can help us reason about the effects of
the computation, but can be ignored when we extract "code" from the
term. Elements of type ``Prop`` are not entirely innocuous,
however. They include equations ``s = t : α`` for any type ``α``, and
such equations can be used as casts, to type check terms. Below, we
will see examples of how such casts can block computation in the
system. However, computation is still possible under an evaluation
scheme that erases propositional content, ignores intermediate typing
constraints, and reduces terms until they reach a normal form. This is
precisely what Lean's virtual machine does.
-->

引入一个与证明无关的 ``Prop`` 并标记定理不可约表示了分离关注点的第一步。
目的是类型为 ``p : Prop`` 的元素在计算中不应发挥任何作用，因此从这个意义上说，
项 ``t : p`` 的特定构造是「无关的」。人们仍然可以定义包含类型为 ``Prop``
的元素的计算对象；关键是这些元素可以帮助我们推理计算的影响，
但在我们从项中提取「代码」时可以忽略。但是，``Prop`` 类型的元素并非完全无害。
它们包括任何类型 ``α`` 的方程 ``s = t : α``，并且此类方程可以作为强制转换使用，
以对项进行类型检查。在后面，我们将看到此类强制转换是如何阻碍系统中的计算的示例。
但是，在擦除命题内容、忽略中间定型约束并归约项，直到它们达到正规形式的求值方案下，
它们仍然可以进行计算。这正是 Lean 的虚拟机所做的。

<!--
Having adopted a proof-irrelevant ``Prop``, one might consider it
legitimate to use, for example, the law of the excluded middle,
``p ∨ ¬p``, where ``p`` is any proposition. Of course, this, too, can block
computation according to the rules of CIC, but it does not block
bytecode evaluation, as described above. It is only the choice
principles discussed in :numref:`choice` that completely erase the
distinction between the proof-irrelevant and data-relevant parts of
the theory.
-->

在通过了证明无关的 ``Prop`` 之后，可以认为使用排中律 ``p ∨ ¬p`` 是合法的，
其中 ``p`` 是任何命题。当然，这也可能根据 CIC 的规则阻止计算，
但它不会阻止字节码求值，如上所述。仅在 :numref:`choice`
中讨论过的选择原则才能完全消除理论中与证明无关的部分和与数据相关部分之间的区别。

<!--
Propositional Extensionality
----------------------------
-->

命题外延性
--------------------

<!--
Propositional extensionality is the following axiom:
-->

命题外延性公理如下：

```lean
# namespace Hidden
axiom propext {a b : Prop} : (a ↔ b) → a = b
# end Hidden
```

<!--
It asserts that when two propositions imply one another, they are
actually equal. This is consistent with set-theoretic interpretations
in which any element ``a : Prop`` is either empty or the singleton set
``{*}``, for some distinguished element ``*``. The axiom has the
effect that equivalent propositions can be substituted for one another
in any context:
-->

它断言当两个命题互相蕴含时，二者实质相等。这与集合论的解释一致，
即对于某个特定的元素 ``*``，其中任何元素 ``a : Prop`` 要么为空集，
要么是单元素集 ``{*}``。此公理具有这样的效果，即等价的命题可以在任何语境中彼此替换：

```lean
theorem thm₁ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₂ (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁
```

<!--
The first example could be proved more laboriously without ``propext``
using the fact that the propositional connectives respect
propositional equivalence. The second example represents a more
essential use of ``propext``. In fact, it is equivalent to ``propext``
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

<!--
Function Extensionality
-----------------------
-->

函数外延性
-----------------------

Similar to propositional extensionality, function extensionality
asserts that any two functions of type ``(x : α) → β x`` that agree on
all their inputs are equal.

```lean
universe u v
#check (@funext :
           {α : Type u}
         → {β : α → Type u}
         → {f g : (x : α) → β x}
         → (∀ (x : α), f x = g x)
         → f = g)

#print funext
```

<!--
From a classical, set-theoretic perspective, this is exactly what it
means for two functions to be equal. This is known as an "extensional"
view of functions. From a constructive perspective, however, it is
sometimes more natural to think of functions as algorithms, or
computer programs, that are presented in some explicit way. It is
certainly the case that two computer programs can compute the same
answer for every input despite the fact that they are syntactically
quite different. In much the same way, you might want to maintain a
view of functions that does not force you to identify two functions
that have the same input / output behavior. This is known as an
"intensional" view of functions.
-->

从经典的集合论角度来看，这正是两个函数相等的确切含义。
它被称作函数的「外延性（Extensional）」视角。然而，从构造主义的角度来看，
有时把函数看作算法，或者以某种明确的方式给出的计算机程序要更加自然。
肯定存在这样的情况：两个计算机程序对每个输入都计算出相同的答案，
尽管它们在语法上非常不同。与此类似，你可能想要维护一种函数的视角，
它不会强迫你将具有相同输入/输出行为的两个函数认定为同样的。
这被称为函数的「内涵（Intensional）」视角。

<!--
In fact, function extensionality follows from the existence of
quotients, which we describe in the next section. In the Lean standard
library, therefore, ``funext`` is thus
[proved from the quotient construction](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean).
-->

实际上，函数外延性来自于商的存在，我们将在下一节中进行描述。
因此，在 Lean 标准库中，`funext` 通过[商的构造来证明](https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean)。

<!--
Suppose that for ``α : Type`` we define the ``Set α := α → Prop`` to
denote the type of subsets of ``α``, essentially identifying subsets
with predicates. By combining ``funext`` and ``propext``, we obtain an
extensional theory of such sets:
-->

假设对于 ``α : Type``，我们定义 ``Set α := α → Prop`` 来表达 ``α`` 子集的类型，
本质上是用谓词来表示子集。通过组合 ``funext`` 和 ``propext``，
我们得到了一个这样的集合的外延性理论：

```lean
def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

end Set
```

<!--
We can then proceed to define the empty set and set intersection, for
example, and prove set identities:
-->

我们可以继续定义例如空集和交集，并证明的集合恒等性：

```lean
# def Set (α : Type u) := α → Prop
# namespace Set
# def mem (x : α) (a : Set α) := a x
# infix:50 (priority := high) "∈" => mem
# theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
#   funext (fun x => propext (h x))
def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
# end Set
```

<!--
The following is an example of how function extensionality blocks
computation inside the Lean kernel.
-->

以下是一个函数外延性阻碍了 Lean 核心中计算的示例：

```lean
def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0

-- 无法归约为 0
#reduce val

-- 求值为 0
#eval val
```

<!--
First, we show that the two functions ``f`` and ``g`` are equal using
function extensionality, and then we cast ``0`` of type ``Nat`` by
replacing ``f`` by ``g`` in the type. Of course, the cast is
vacuous, because ``Nat`` does not depend on ``f``. But that is enough
to do the damage: under the computational rules of the system, we now
have a closed term of ``Nat`` that does not reduce to a numeral. In this
case, we may be tempted to reduce the expression to ``0``. But in
nontrivial examples, eliminating cast changes the type of the term,
which might make an ambient expression type incorrect. The virtual
machine, however, has no trouble evaluating the expression to
``0``. Here is a similarly contrived example that shows how
``propext`` can get in the way.
-->

首先，我们使用函数外延性来证明两个函数 ``f`` 和 ``g`` 相等，
然后用 ``g`` 替换类型为 ``Nat`` 的 ``f``，从而转换该类型。
当然，转换是无意义的，因为 ``Nat`` 不依赖于 ``f``。
但这已经足够了：在系统的计算规则之下，我们现在有了 ``Nat`` 的一个封闭项，
它不会归约为一个数值。在这种情况下，我们可能倾向于将该表达式归约为 ``0``。
但是，在非平凡的例子里，消除转换会改变该项的类型，这可能会导致周围的表达式类型不正确。
然而，虚拟机将表达式求值为 ``0`` 则不会遇到问题。下面是一个类似的例子，
展示了 ``propext`` 如何造成阻碍。

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

<!--
Current research programs, including work on *observational type
theory* and *cubical type theory*, aim to extend type theory in ways
that permit reductions for casts involving function extensionality,
quotients, and more. But the solutions are not so clear cut, and the
rules of Lean's underlying calculus do not sanction such reductions.
-->

当前的研究计划包括关于 **观测类型论（Observational Type Theory）**
和 **立方类型论（Cubical Type Theory）** 的研究，旨在扩展类型理论，
以便允许对涉及函数外延、商，等等的强制转换进行归约。
但解决方案并不明朗，而 Lean 的底层演算法则对此类归约也不支持。

<!--
In a sense, however, a cast does not change the meaning of an
expression. Rather, it is a mechanism to reason about the expression's
type. Given an appropriate semantics, it then makes sense to reduce
terms in ways that preserve their meaning, ignoring the intermediate
bookkeeping needed to make the reductions type correct. In that case,
adding new axioms in ``Prop`` does not matter; by proof irrelevance,
an expression in ``Prop`` carries no information, and can be safely
ignored by the reduction procedures.
-->

从某种意义上来说，一个强制转换不会改变一个表达式的含义。
相反，它是一种关于表达式类型的推理机制。给定一个适当的语义，
那么忽略掉归约为正确类型所需的中间记录操作，以不改变其含义的方式归约项是有意义的。
在这种情况下，在 ``Prop`` 中添加新公理并不重要；通过证明无关性，
``Prop`` 中的表达式不会承载任何信息，可以被归约过程安全地忽略。

<!--
Quotients
---------
-->

商
---------

<!--
Let ``α`` be any type, and let ``r`` be an equivalence relation on
``α``. It is mathematically common to form the "quotient" ``α / r``,
that is, the type of elements of ``α`` "modulo" ``r``. Set
theoretically, one can view ``α / r`` as the set of equivalence
classes of ``α`` modulo ``r``. If ``f : α → β`` is any function that
respects the equivalence relation in the sense that for every
``x y : α``, ``r x y`` implies ``f x = f y``, then ``f`` "lifts" to a function
``f' : α / r → β`` defined on each equivalence class ``⟦x⟧`` by
``f' ⟦x⟧ = f x``. Lean's standard library extends the Calculus of
Constructions with additional constants that perform exactly these
constructions, and installs this last equation as a definitional
reduction rule.
-->

设 ``α`` 为任意类型，且 ``r`` 为 ``α`` 上的等价关系。在数学中，
常见的做法是形成「商（Quotient）」``α / r``，即 ``α`` 中元素的类型「模（modulo）」``r``。
从集合论的角度，可以将 ``α / r`` 视为 ``α`` 模 ``r`` 的等价类的集合。
若 ``f : α → β`` 是任意满足等价关系的函数，即对于任意 ``x y : α``, ``r x y``
蕴含 ``f x = f y``, 则 ``f``「提升（lift）」到函数 ``f' : α / r → β``，
其在每个等价类 ``⟦x⟧`` 上由 ``f' ⟦x⟧ = f x`` 定义。
Lean 的标准库通过执行这些构造的附加常量来扩展构造演算，并将该最后的方程作为定义归约规则。

<!--
In its most basic form, the quotient construction does not even
require ``r`` to be an equivalence relation. The following constants
are built into Lean:
-->

在最基本的表述形式中，商构造甚至不需要 ``r`` 成为一个等价关系。
下列常量被内置在 Lean 中：

```lean
# namespace Hidden
universe u v

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β
# end Hidden
```

<!--
The first one forms a type ``Quot r`` given a type ``α`` by any binary
relation ``r`` on ``α``. The second maps ``α`` to ``Quot α``, so that
if ``r : α → α → Prop`` and ``a : α``, then ``Quot.mk r a`` is an
element of ``Quot r``. The third principle, ``Quot.ind``, says that
every element of ``Quot.mk r a`` is of this form.  As for
``Quot.lift``, given a function ``f : α → β``, if ``h`` is a proof
that ``f`` respects the relation ``r``, then ``Quot.lift f h`` is the
corresponding function on ``Quot r``. The idea is that for each
element ``a`` in ``α``, the function ``Quot.lift f h`` maps
``Quot.mk r a`` (the ``r``-class containing ``a``) to ``f a``, wherein ``h``
shows that this function is well defined. In fact, the computation
principle is declared as a reduction rule, as the proof below makes
clear.
-->

第一条公理根据任何二元关系 ``r`` 的类型 ``α`` 形成类型 ``Quot r``。
第二条公理将 ``α`` 映射到 ``Quot α``，因此若 ``r : α → α → Prop`` 且 ``a : α``，
则 ``Quot.mk r a`` 是 ``Quot r`` 的一个元素。
第三条公理 ``Quot.ind`` 是说 ``Quot.mk r a`` 的每个元素都属于此形式。
至于 ``Quot.lift``，给定函数 ``f : α → β``，若 ``h`` 是一个「``f``
遵循关系 ``r``」的证明，则 ``Quot.lift f h`` 是 ``Quot r`` 上的对应函数。
其思想是对于 ``α`` 中的每个元素 ``a``，函数 ``Quot.lift f h``
将 ``Quot.mk r a``（包含 ``a`` 的 ``r``-类）映射到 ``f a``，
其中 ``h`` 表明此函数是良定义的。事实上，计算公理被声明为一个归约规则，
如下方的证明所示。

```lean
def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- the quotient type
#check (Quot mod7Rel : Type)

-- the class of a
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

<!--
The four constants, ``Quot``, ``Quot.mk``, ``Quot.ind``, and
``Quot.lift`` in and of themselves are not very strong. You can check
that the ``Quot.ind`` is satisfied if we take ``Quot r`` to be simply
``α``, and take ``Quot.lift`` to be the identity function (ignoring
``h``). For that reason, these four constants are not viewed as
additional axioms.
-->

四个常量 ``Quot``、``Quot.mk``、``Quot.ind`` 和 ``Quot.lift`` 在它们本身上并不强。
你可以检查如果我们把 ``Quot r`` 简单地取为 ``α``，并取 ``Quot.lift`` 为恒等函数
（忽略 ``h``），那么 ``Quot.ind`` 将得到满足。
由于这个原因，这四个常量并没有被看作附加公理。

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

<!--
They are, like inductively defined types and the associated
constructors and recursors, viewed as part of the logical framework.
-->

和归纳定义的类型以及相关的构造子和递归器一样，它们也被视为逻辑框架的一部分。

<!--
What makes the ``Quot`` construction into a bona fide quotient is the
following additional axiom:
-->

使 ``Quot`` 构造成为真正商的是以下一个附加公理：

```lean
# namespace Hidden
# universe u v
axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
# end Hidden
```

<!--
This is the axiom that asserts that any two elements of ``α`` that are
related by ``r`` become identified in the quotient. If a theorem or
definition makes use of ``Quot.sound``, it will show up in the
``#print axioms`` command.
-->

这条公理断言 ``α`` 的任何两个元素，只要满足关系 ``r``，就能在商中被识别的。
如果定理或定义使用了 ``Quot.sound``，它将会在 ``#print axioms`` 命令中显示。

<!--
Of course, the quotient construction is most commonly used in
situations when ``r`` is an equivalence relation. Given ``r`` as
above, if we define ``r'`` according to the rule ``r' a b`` iff
``Quot.mk r a = Quot.mk r b``, then it's clear that ``r'`` is an
equivalence relation. Indeed, ``r'`` is the *kernel* of the function
``a ↦ quot.mk r a``.  The axiom ``Quot.sound`` says that ``r a b``
implies ``r' a b``. Using ``Quot.lift`` and ``Quot.ind``, we can show
that ``r'`` is the smallest equivalence relation containing ``r``, in
the sense that if ``r''`` is any equivalence relation containing
``r``, then ``r' a b`` implies ``r'' a b``. In particular, if ``r``
was an equivalence relation to start with, then for all ``a`` and
``b`` we have ``r a b`` iff ``r' a b``.
-->

当然，当 ``r`` 是等价关系时，商集的结构是最常用的。给定上面的 ``r``，
如果我们根据法则 ``r' a b`` 当且仅当 ``Quot.mk r a = Quot.mk r b`` 定义 ``r'``，
那么显然 ``r'`` 就是一个等价关系。事实上，``r'`` 是函数 ``a ↦ quot.mk r a``
的 **核（Kernel）** 。公理 ``Quot.sound`` 表明 ``r a b`` 蕴含 ``r' a b``。
使用 ``Quot.lift`` 和 ``Quot.ind``，我们可以证明 ``r'`` 是包含 ``r`` 的最小的等价关系，
意思就是，如果 ``r''`` 是包含 ``r`` 的任意等价关系，则 ``r' a b`` 蕴含 ``r'' a b``。
特别地，如果 ``r`` 开始就是一个等价关系，那么对任意 ``a`` 和 ``b``，我们都有
``r a b`` 等价于 ``r' a b``。

<!--
To support this common use case, the standard library defines the
notion of a *setoid*, which is simply a type with an associated
equivalence relation:
-->

为支持这种通用使用案例，标准库定义了  **广集（Setoid）**  的概念，
它只是一个带有与之关联的等价关系的类型：

```lean
# namespace Hidden
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
# end Hidden
```

<!--
Given a type ``α``, a relation ``r`` on ``α``, and a proof ``p``
that ``r`` is an equivalence relation, we can define ``Setoid.mk r p``
as an instance of the setoid class.
-->

给定一个类型 ``α`` 和其上的关系 ``r``，以及一个证明 ``p`` 证明 ``r`` 是一个等价关系，
我们可以定义 ``Setoid.mk r p`` 为广集类的一个实例。

```lean
# namespace Hidden
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r
# end Hidden
```

<!--
The constants ``Quotient.mk``, ``Quotient.ind``, ``Quotient.lift``,
and ``Quotient.sound`` are nothing more than the specializations of
the corresponding elements of ``Quot``. The fact that type class
inference can find the setoid associated to a type ``α`` brings a
number of benefits. First, we can use the notation ``a ≈ b`` (entered
with ``\approx``) for ``Setoid.r a b``, where the instance of
``Setoid`` is implicit in the notation ``Setoid.r``. We can use the
generic theorems ``Setoid.refl``, ``Setoid.symm``, ``Setoid.trans`` to
reason about the relation. Specifically with quotients we can use the
generic notation ``⟦a⟧`` for ``Quot.mk Setoid.r`` where the instance
of ``Setoid`` is implicit in the notation ``Setoid.r``, as well as the
theorem ``Quotient.exact``:
-->

常量 ``Quotient.mk``、``Quotient.ind``、``Quotient.lift``
以及 ``Quotient.sound`` 仅为 ``Quot`` 对应元素的特化形式。
类型类推断能找到与类型 ``α`` 关联的广集，这带来了大量好处。
首先，我们可以对 ``Setoid.r a b`` 使用符号 ``a ≈ b``（用 ``\approx`` 输入），
其中 ``Setoid`` 的实例在符号 ``Setoid.r`` 中是内隐的。
我们可以使用通用定理 ``Setoid.refl``、``Setoid.symm``、``Setoid.trans``
来推断关系。具体来说，在商中，我们可以对 ``Quot.mk Setoid.r`` 使用通用符号 ``⟦a⟧``，
其中 ``Setoid`` 的实例在符号 ``Setoid.r`` 中是内隐的，以及定理 ``Quotient.exact``：

```lean
# universe u
#check (@Quotient.exact :
         ∀ {α : Sort u} {s : Setoid α} {a b : α},
           Quotient.mk s a = Quotient.mk s b → a ≈ b)
```

<!--
Together with ``Quotient.sound``, this implies that the elements of
the quotient correspond exactly to the equivalence classes of elements
in ``α``.
-->

结合 ``Quotient.sound``，这意味着商的各个元素精确对应于 ``α`` 中各元素的等价类。

<!--
Recall that in the standard library, ``α × β`` represents the
Cartesian product of the types ``α`` and ``β``. To illustrate the use
of quotients, let us define the type of *unordered* pairs of elements
of a type ``α`` as a quotient of the type ``α × α``. First, we define
the relevant equivalence relation:
-->

回顾一下标准库中的 ``α × β`` 代表类型 ``α`` 和 ``β`` 的笛卡尔积。
为了说明商的用法，让我们将类型为 ``α`` 的元素构成的 **无序对（Unordered Pair）** 的类型定义为
``α × α`` 类型的商。首先，我们定义相关的等价关系：

```lean
private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv
```

<!--
The next step is to prove that ``eqv`` is in fact an equivalence
relation, which is to say, it is reflexive, symmetric and
transitive. We can prove these three facts in a convenient and
readable way by using dependent pattern matching to perform
case-analysis and break the hypotheses into pieces that are then
reassembled to produce the conclusion.
-->

下一步是证明 ``eqv`` 实际上是一个等价关系，即满足自反性、对称性和传递性。
我们可以使用依值模式匹配进行情况分析，将假设分解然后重新组合以得出结论，
从而以一种简便易读的方式证明这三个事实。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
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

<!--
Now that we have proved that ``eqv`` is an equivalence relation, we
can construct a ``Setoid (α × α)``, and use it to define the type
``UProd α`` of unordered pairs.
-->

现在我们已经证明了 ``eqv`` 是一个等价关系，我们可以构造一个 ``Setoid (α × α)``，
并使用它来定义无序对的类型 ``UProd α``。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#   Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
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

<!--
Notice that we locally define the notation ``{a₁, a₂}`` for unordered
pairs as ``Quotient.mk (a₁, a₂)``. This is useful for illustrative
purposes, but it is not a good idea in general, since the notation
will shadow other uses of curly brackets, such as for records and
sets.
-->

请注意，我们将 ``{a₁, a₂}`` 无序对的记法局部定义为 ``Quotient.mk (a₁, a₂)``。
这对展示来说很有用，但一般来说这不是一个好主意，因为该记法将会与花括号的其它用法冲突，
例如记录和集合。

<!--
We can easily prove that ``{a₁, a₂} = {a₂, a₁}`` using ``Quot.sound``,
since we have ``(a₁, a₂) ~ (a₂, a₁)``.
-->

我们可以很容易地使用 ``Quot.sound`` 证明 ``{a₁, a₂} = {a₂, a₁}``，
因为我们有 ``(a₁, a₂) ~ (a₂, a₁)``。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#   Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
# instance uprodSetoid (α : Type u) : Setoid (α × α) where
#   r     := eqv
#   iseqv := is_equivalence
# def UProd (α : Type u) : Type u :=
#   Quotient (uprodSetoid α)
# namespace UProd
# def mk {α : Type} (a₁ a₂ : α) : UProd α :=
#   Quotient.mk' (a₁, a₂)
# notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)
# end UProd
```

<!--
To complete the example, given ``a : α`` and ``u : uprod α``, we
define the proposition ``a ∈ u`` which should hold if ``a`` is one of
the elements of the unordered pair ``u``. First, we define a similar
proposition ``mem_fn a u`` on (ordered) pairs; then we show that
``mem_fn`` respects the equivalence relation ``eqv`` with the lemma
``mem_respects``. This is an idiom that is used extensively in the
Lean standard library.
-->

为了完成此示例，给定 ``a : α`` 和 ``u : uprod α``，我们定义命题 ``a ∈ u``，
若 ``a`` 是无序对 ``u`` 的元素之一，则该命题应成立。
首先，我们在（有序）对上定义一个类似的命题 ``mem_fn a u``；
然后用引理 ``mem_respects`` 证明 ``mem_fn`` 关于等价关系 ``eqv`` 成立。
这是一个在 Lean 标准库中广泛使用的惯用法。

```lean
# private def eqv (p₁ p₂ : α × α) : Prop :=
#   (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
# infix:50 " ~ " => eqv
# private theorem eqv.refl (p : α × α) : p ~ p :=
#   Or.inl ⟨rfl, rfl⟩
# private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
#   | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
#     Or.inr (by simp_all)
# private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inl (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
#     Or.inr (by simp_all)
#   | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
#     Or.inl (by simp_all)
# private theorem is_equivalence : Equivalence (@eqv α) :=
#   { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }
# instance uprodSetoid (α : Type u) : Setoid (α × α) where
#   r     := eqv
#   iseqv := is_equivalence
# def UProd (α : Type u) : Type u :=
#   Quotient (uprodSetoid α)
# namespace UProd
# def mk {α : Type} (a₁ a₂ : α) : UProd α :=
#   Quotient.mk' (a₁, a₂)
# notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
# theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
#   Quot.sound (Or.inr ⟨rfl, rfl⟩)
private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

-- auxiliary lemma for proving mem_respects
-- 用于证明 mem_respects 的辅助引理
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


private theorem mem_respects
      : {p₁ p₂ : α × α} → (a : α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by simp_all; apply mem_swap

def mem (a : α) (u : UProd α) : Prop :=
  Quot.liftOn u (fun p => mem_fn a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 (priority := high) " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
  fun h => h
# end UProd
```

<!--
For convenience, the standard library also defines ``Quotient.lift₂``
for lifting binary functions, and ``Quotient.ind₂`` for induction on
two variables.
-->

为方便起见，标准库还定义了二元函数的 ``Quotient.lift₂``，
以及对于两个变量的归纳的 ``Quotient.ind₂``。

<!--
We close this section with some hints as to why the quotient
construction implies function extensionality. It is not hard to show
that extensional equality on the ``(x : α) → β x`` is an equivalence
relation, and so we can consider the type ``extfun α β`` of functions
"up to equivalence." Of course, application respects that equivalence
in the sense that if ``f₁`` is equivalent to ``f₂``, then ``f₁ a`` is
equal to ``f₂ a``. Thus application gives rise to a function
``extfun_app : extfun α β → (x : α) → β x``. But for every ``f``,
``extfun_app ⟦f⟧`` is definitionally equal to ``fun x => f x``, which is
in turn definitionally equal to ``f``. So, when ``f₁`` and ``f₂`` are
extensionally equal, we have the following chain of equalities:
-->

我们在本节的末尾解释为什么商构造蕴含了函数的外延性。不难证明在 ``(x : α) → β x``
上的外延相等性是一种等价关系，因此我们可以将类型 ``extfun α β`` 视为「保持等价」的函数。
当然，函数应用遵循这种等价，即若 `f₁` 等价于 `f₂`，则 `f₁ a` 等于 `f₂ a`。
因此，应用产生了一个函数 ``extfun_app : extfun α β → (x : α) → β x``。
但是对于每个 `f` 而言，``extfun_app ⟦f⟧`` 在定义上等于 ``fun x => f x``，
这在定义上又等于 ``f``。所以，当 `f₁` 和 `f₂` 外延相等时，我们有以下等式链：

```
    f₁ = extfun_app ⟦f₁⟧ = extfun_app ⟦f₂⟧ = f₂
```

<!--
As a result, ``f₁`` is equal to ``f₂``.
-->

因此，``f₁`` 等于 ``f₂``。

<!--
Choice
------
-->

选择公理
--------

<!--
To state the final axiom defined in the standard library, we need the
``Nonempty`` type, which is defined as follows:
-->

为了陈述标准库中定义的最后一个公理，我们需要 ``Nonempty`` 类型，它的定义如下：

```lean
# namespace Hidden
class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α
# end Hidden
```

<!--
Because ``Nonempty α`` has type ``Prop`` and its constructor contains data, it can only eliminate to ``Prop``.
In fact, ``Nonempty α`` is equivalent to ``∃ x : α, True``:
-->

由于 ``Nonempty α`` 的类型为 ``Prop``，其构造子包含数据，所以只能消去到 ``Prop``。
事实上，``Nonempty α`` 等价于 ``∃ x : α, True``：

```lean
example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro (fun ⟨a⟩ => ⟨a, trivial⟩) (fun ⟨a, h⟩ => ⟨a⟩)
```

<!--
Our axiom of choice is now expressed simply as follows:
-->

我们的选择公理现在可以简单地表示如下：

```lean
# namespace Hidden
# universe u
axiom choice {α : Sort u} : Nonempty α → α
# end Hidden
```

<!--
Given only the assertion ``h`` that ``α`` is nonempty, ``choice h``
magically produces an element of ``α``. Of course, this blocks any
meaningful computation: by the interpretation of ``Prop``, ``h``
contains no information at all as to how to find such an element.
-->

给定唯一断言 ``h``，即 ``α`` 非空，``choice h`` 神奇地产生了一个 ``α`` 的元素。
当然，这阻碍了任何有意义的计算：根据 ``Prop`` 的解释，``h`` 根本不包含任何信息，
因而无法找到这样的元素。

<!--
This is found in the ``Classical`` namespace, so the full name of the
theorem is ``Classical.choice``. The choice principle is equivalent to
the principle of *indefinite description*, which can be expressed with
subtypes as follows:
-->

这可以在 ``Classical`` 命名空间中找到，所以定理的全名是 ``Classical.choice``。
选择公理等价于 **非限定摹状词（Indefinite Description）** 原理，可通过子类型表示如下：

```lean
# namespace Hidden
# universe u
# axiom choice {α : Sort u} : Nonempty α → α
noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop)
                                        (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩
# end Hidden
```

<!--
Because it depends on ``choice``, Lean cannot generate bytecode for
``indefiniteDescription``, and so requires us to mark the definition
as ``noncomputable``. Also in the ``Classical`` namespace, the
function ``choose`` and the property ``choose_spec`` decompose the two
parts of the output of ``indefiniteDescription``:
-->

因为依赖于 ``choice``，Lean 不能为 ``indefiniteDescription`` 生成字节码，
所以要求我们将定义标记为 ``noncomputable``。同样在 ``Classical`` 命名空间中，
函数 ``choose`` 和属性 ``choose_spec`` 分离了 ``indefiniteDescription`` 输出的两个部分：

```lean
# open Classical
# namespace Hidden
noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
# end Hidden
```

<!--
The ``choice`` principle also erases the distinction between the
property of being ``Nonempty`` and the more constructive property of
being ``Inhabited``:
-->

``choice`` 选择公理也消除了 ``Nonempty`` 特性与更加具有构造性的
``Inhabited`` 特性之间的区别。

```lean
# open Classical
theorem inhabited_of_nonempty : Nonempty α → Inhabited α :=
  fun h => choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)
```

<!--
In the next section, we will see that ``propext``, ``funext``, and
``choice``, taken together, imply the law of the excluded middle and
the decidability of all propositions. Using those, one can strengthen
the principle of indefinite description as follows:
-->

在下一节中，我们将会看到 ``propext``、``funext`` 和 ``choice``，
合起来就构成了排中律以及所有命题的可判定性。使用它们，我们可以加强如下非限定摹状词原理：

```lean
# open Classical
# universe u
#check (@strongIndefiniteDescription :
         {α : Sort u} → (p : α → Prop)
         → Nonempty α → {x // (∃ (y : α), p y) → p x})
```

<!--
Assuming the ambient type ``α`` is nonempty,
``strongIndefiniteDescription p`` produces an element of ``α``
satisfying ``p`` if there is one. The data component of this
definition is conventionally known as *Hilbert's epsilon function*:
-->

假设环境类型 ``α`` 非空，``strongIndefiniteDescription p`` 产生一个满足 ``p``
的元素 ``α``（如果存在的话）。该定义的数据部分通常被称为  **希尔伯特 ε 函数** ：

```lean
# open Classical
# universe u
#check (@epsilon :
         {α : Sort u} → [Nonempty α]
         → (α → Prop) → α)

#check (@epsilon_spec :
         ∀ {α : Sort u} {p : α → Prop} (hex : ∃ (y : α), p y),
           p (@epsilon _ (nonempty_of_exists hex) p))
```

<!--
The Law of the Excluded Middle
------------------------------
-->

排中律
------

<!--
The law of the excluded middle is the following
-->

排中律如下所示：

```lean
open Classical

#check (@em : ∀ (p : Prop), p ∨ ¬p)
```

<!--
[Diaconescu's theorem](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem) states
that the axiom of choice is sufficient to derive the law of excluded
middle. More precisely, it shows that the law of the excluded middle
follows from ``Classical.choice``, ``propext``, and ``funext``. We
sketch the proof that is found in the standard library.
-->

[迪亚科内斯库定理](https://en.wikipedia.org/wiki/Diaconescu%27s_theorem) 表明
选择公理足以导出排中律。更确切地说，它表明排中律源自于 ``Classical.choice``，
``propext`` 和 ``funext``。我们概述了标准库中的证明。

<!--
First, we import the necessary axioms, and define two predicates ``U`` and ``V``:
-->

首先，我们导入必要的公理，并定义两个谓词 ``U`` 和 ``V``：

```lean
# namespace Hidden
open Classical
theorem em (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p

  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   sorry
# end Hidden
```

<!--
If ``p`` is true, then every element of ``Prop`` is in both ``U`` and ``V``.
If ``p`` is false, then ``U`` is the singleton ``true``, and ``V`` is the singleton ``false``.
-->

当 ``p`` 为真时，``Prop`` 的所有元素既在 ``U`` 中又在 ``V`` 中。
当 ``p`` 为假时，``U`` 是单元素的 ``true``，``V`` 是单元素的 ``false``。

<!--
Next, we use ``some`` to choose an element from each of ``U`` and ``V``:
-->

接下来，我们使用 ``some`` 从 ``U`` 和 ``V`` 中各选取一个元素：

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV

  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
#   sorry
# end Hidden
```

<!--
Each of ``U`` and ``V`` is a disjunction, so ``u_def`` and ``v_def``
represent four cases. In one of these cases, ``u = True`` and
``v = False``, and in all the other cases, ``p`` is true. Thus we have:
-->

``U`` 和 ``V`` 都是析取，所以 ``u_def`` 和 ``v_def`` 表示四种情况。
在其中一种情况下，``u = True`` 且 ``v = False``，在所有其他情况下，
``p`` 为真。因此我们有：

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
#   sorry
# end Hidden
```

<!--
On the other hand, if ``p`` is true, then, by function extensionality
and propositional extensionality, ``U`` and ``V`` are equal. By the
definition of ``u`` and ``v``, this implies that they are equal as well.
-->

另一方面，若 ``p`` 为真，则由函数的外延性和命题的外延性，可得 ``U`` 和 ``V`` 相等。
根据 ``u`` 和 ``v`` 的定义，这蕴含了它们也相等。

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
#   have not_uv_or_p : u ≠ v ∨ p :=
#     match u_def, v_def with
#     | Or.inr h, _ => Or.inr h
#     | _, Or.inr h => Or.inr h
#     | Or.inl hut, Or.inl hvf =>
#       have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
#       Or.inl hne
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
#   sorry
# end Hidden
```

<!--
Putting these last two facts together yields the desired conclusion:
-->

将最后两个事实放在一起可以得出期望的结论：

```lean
# namespace Hidden
# open Classical
# theorem em (p : Prop) : p ∨ ¬p :=
#   let U (x : Prop) : Prop := x = True ∨ p
#   let V (x : Prop) : Prop := x = False ∨ p
#   have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
#   have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
#   let u : Prop := choose exU
#   let v : Prop := choose exV
#   have u_def : U u := choose_spec exU
#   have v_def : V v := choose_spec exV
#   have not_uv_or_p : u ≠ v ∨ p :=
#     match u_def, v_def with
#     | Or.inr h, _ => Or.inr h
#     | _, Or.inr h => Or.inr h
#     | Or.inl hut, Or.inl hvf =>
#       have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
#       Or.inl hne
#   have p_implies_uv : p → u = v :=
#     fun hp =>
#     have hpred : U = V :=
#       funext fun x =>
#         have hl : (x = True ∨ p) → (x = False ∨ p) :=
#           fun _ => Or.inr hp
#         have hr : (x = False ∨ p) → (x = True ∨ p) :=
#           fun _ => Or.inr hp
#         show (x = True ∨ p) = (x = False ∨ p) from
#           propext (Iff.intro hl hr)
#     have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
#       rw [hpred]; intros; rfl
#     show u = v from h₀ _ _
  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h
# end Hidden
```

<!--
Consequences of excluded middle include double-negation elimination,
proof by cases, and proof by contradiction, all of which are described
in the [Section Classical Logic](./propositions_and_proofs.md#classical-logic).
The law of the excluded middle and propositional extensionality imply propositional completeness:
-->

排除中律的推论包括双重否定消除、分情况证明和反证法，
所有这些都在 [经典逻辑一节](./propositions_and_proofs.md#classical-logic)
中描述。排除中律和命题外延性律蕴含了命题完备性：

```lean
# namespace Hidden
open Classical
theorem propComplete (a : Prop) : a = True ∨ a = False :=
  match em a with
  | Or.inl ha => Or.inl (propext (Iff.intro (fun _ => ⟨⟩) (fun _ => ha)))
  | Or.inr hn => Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))
# end Hidden
```

<!--
Together with choice, we also get the stronger principle that every
proposition is decidable. Recall that the class of ``Decidable``
propositions is defined as follows:
-->

有了选择公理，我们也能得到一个更强的原则，即每个命题都是可判定的。
回想一下 ``Decidable`` 可判定性命题集定义如下:

```lean
# namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
# end Hidden
```

<!--
In contrast to ``p ∨ ¬ p``, which can only eliminate to ``Prop``, the
type ``Decidable p`` is equivalent to the sum type ``Sum p (¬ p)``, which
can eliminate to any type. It is this data that is needed to write an
if-then-else expression.
-->

与 ``p ∨ ¬ p`` 不同，它只能消去到 ``Prop``，类型 ``Decidable p`` 等效于和类型
``Sum p (¬ p)``，它可以消除至任何类型。
这就是编写「if-then-else（若-则-否则）」表达式所需的数据。

<!--
As an example of classical reasoning, we use ``choose`` to show that if
``f : α → β`` is injective and ``α`` is inhabited, then ``f`` has a
left inverse. To define the left inverse ``linv``, we use a dependent
if-then-else expression. Recall that ``if h : c then t else e`` is
notation for ``dite c (fun h : c => t) (fun h : ¬ c => e)``. In the definition
of ``linv``, choice is used twice: first, to show that
``(∃ a : A, f a = b)`` is "decidable," and then to choose an ``a`` such that
``f a = b``. Notice that ``propDecidable`` is a scoped instance and is activated
by the `open Classical` command. We use this instance to justify
the if-then-else expression. (See also the discussion in
[Section Decidable Propositions](./type_classes.md#decidable-propositions)).
-->

作为经典推理的一个示例，我们使用 ``choose`` 来证明，若 ``f : α → β`` 是单射的，
且 ``α`` 是可居的，则 ``f`` 是左逆的。为了定义左逆 ``linv``，我们使用一个依值的
if-then-else 表达式。回忆一下，``if h : c then t else e`` 是
``dite c (fun h : c => t) (fun h : ¬ c => e)`` 的记法。在 ``linv`` 的定义中，
选择公理使用了两次：首先，为了证明 ``(∃ a : A, f a = b)`` 是「可判定的」，
需要选择一个 ``a``，使得 ``f a = b``。请注意，``propDecidable`` 是一个作用域实例，
它通过 `open Classical` 命令激活。我们使用此实例来证明 if-then-else 表达式。
（还可以参阅 [可判命题一节](./type_classes.md#decidable-propositions) 中的讨论）。

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
      _ = choose ex := dif_pos ex
      _ = a         := inj feq
```

<!--
From a classical point of view, ``linv`` is a function. From a
constructive point of view, it is unacceptable; because there is no
way to implement such a function in general, the construction is not
informative.
-->

从经典逻辑的视角来看，``linv`` 是一个函数。而从构造性视角来看，
它是不可接受的；由于没有实现这样一种函数的通用方法，因此该构造不具备信息量。
