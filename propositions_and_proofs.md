<!--
Propositions and Proofs
=======================
-->

命题和证明
=======================

<!--
By now, you have seen some ways of defining objects and functions in
Lean. In this chapter, we will begin to explain how to write
mathematical assertions and proofs in the language of dependent type
theory as well.
-->

前一章你已经看到了在 Lean 中定义对象和函数的一些方法。在本章中，我们还将开始解释如何用依值类型论的语言来编写数学命题和证明。

<!--
Propositions as Types
---------------------
-->

命题即类型
---------------------

<!--
One strategy for proving assertions about objects defined in the
language of dependent type theory is to layer an assertion language
and a proof language on top of the definition language. But there is
no reason to multiply languages in this way: dependent type theory is
flexible and expressive, and there is no reason we cannot represent
assertions and proofs in the same general framework.

For example, we could introduce a new type, ``Prop``, to represent
propositions, and introduce constructors to build new propositions
from others.
-->

证明在依值类型论语言中定义的对象的断言（assertion）的一种策略是在定义语言之上分层断言语言和证明语言。但是，没有理由以这种方式重复使用多种语言：依值类型论是灵活和富有表现力的，我们也没有理由不能在同一个总框架中表示断言和证明。

例如，我们可引入一种新类型 ``Prop``，来表示命题，然后引入用其他命题构造新命题的构造子。

```lean
# def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop
```

<!--
We could then introduce, for each element ``p : Prop``, another type
``Proof p``, for the type of proofs of ``p``.  An "axiom" would be a
constant of such a type.
-->

对每个元素 ``p : Prop``，可以引入另一个类型 ``Proof p``，作为 ``p`` 的证明的类型。「公理」是这个类型中的常值。

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
#check Proof   -- Proof : Prop → Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm p q     -- Proof (Implies (And p q) (And q p))
```

<!--
In addition to axioms, however, we would also need rules to build new
proofs from old ones. For example, in many proof systems for
propositional logic, we have the rule of modus ponens:

> From a proof of ``Implies p q`` and a proof of ``p``, we obtain a proof of ``q``.

We could represent this as follows:
-->

然而，除了公理之外，我们还需要从旧证明中建立新证明的规则。例如，在许多命题逻辑的证明系统中，我们有肯定前件式（modus ponens）推理规则:

> 如果能证明 ``Implies p q`` 和 ``p``，则能证明 ``q``。

我们可以如下地表示它：

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
```

<!--
Systems of natural deduction for propositional logic also typically rely on the following rule:

> Suppose that, assuming ``p`` as a hypothesis, we have a proof of ``q``. Then we can "cancel" the hypothesis and obtain a proof of ``Implies p q``.

We could render this as follows:
-->

命题逻辑的自然演绎系统通常也依赖于以下规则：

> 当假设 ``p`` 成立时，如果我们能证明 ``q``. 则我们能证明 ``Implies p q``.

我们可以如下地表示它：

```lean
# def Implies (p q : Prop) : Prop := p → q
# structure Proof (p : Prop) : Type where
#   proof : p
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)
```

<!--
This approach would provide us with a reasonable way of building assertions and proofs.
Determining that an expression ``t`` is a correct proof of assertion ``p`` would then
simply be a matter of checking that ``t`` has type ``Proof p``.

Some simplifications are possible, however. To start with, we can
avoid writing the term ``Proof`` repeatedly by conflating ``Proof p``
with ``p`` itself. In other words, whenever we have ``p : Prop``, we
can interpret ``p`` as a type, namely, the type of its proofs. We can
then read ``t : p`` as the assertion that ``t`` is a proof of ``p``.

Moreover, once we make this identification, the rules for implication
show that we can pass back and forth between ``Implies p q`` and
``p → q``. In other words, implication between propositions ``p`` and ``q``
corresponds to having a function that takes any element of ``p`` to an
element of ``q``. As a result, the introduction of the connective
``Implies`` is entirely redundant: we can use the usual function space
constructor ``p → q`` from dependent type theory as our notion of
implication.

This is the approach followed in the Calculus of Constructions, and
hence in Lean as well. The fact that the rules for implication in a
proof system for natural deduction correspond exactly to the rules
governing abstraction and application for functions is an instance of
the *Curry-Howard isomorphism*, sometimes known as the
*propositions-as-types* paradigm. In fact, the type ``Prop`` is
syntactic sugar for ``Sort 0``, the very bottom of the type hierarchy
described in the last chapter. Moreover, ``Type u`` is also just
syntactic sugar for ``Sort (u+1)``. ``Prop`` has some special
features, but like the other type universes, it is closed under the
arrow constructor: if we have ``p q : Prop``, then ``p → q : Prop``.

There are at least two ways of thinking about propositions as
types. To some who take a constructive view of logic and mathematics,
this is a faithful rendering of what it means to be a proposition: a
proposition ``p`` represents a sort of data type, namely, a
specification of the type of data that constitutes a proof. A proof of
``p`` is then simply an object ``t : p`` of the right type.

Those not inclined to this ideology can view it, rather, as a simple
coding trick. To each proposition ``p`` we associate a type that is
empty if ``p`` is false and has a single element, say ``*``, if ``p``
is true. In the latter case, let us say that (the type associated
with) ``p`` is *inhabited*. It just so happens that the rules for
function application and abstraction can conveniently help us keep
track of which elements of ``Prop`` are inhabited. So constructing an
element ``t : p`` tells us that ``p`` is indeed true. You can think of
the inhabitant of ``p`` as being the "fact that ``p`` is true." A
proof of ``p → q`` uses "the fact that ``p`` is true" to obtain "the
fact that ``q`` is true."

Indeed, if ``p : Prop`` is any proposition, Lean's kernel treats any
two elements ``t1 t2 : p`` as being definitionally equal, much the
same way as it treats ``(fun x => t) s`` and ``t[s/x]`` as
definitionally equal. This is known as *proof irrelevance,* and is
consistent with the interpretation in the last paragraph. It means
that even though we can treat proofs ``t : p`` as ordinary objects in
the language of dependent type theory, they carry no information
beyond the fact that ``p`` is true.

The two ways we have suggested thinking about the
propositions-as-types paradigm differ in a fundamental way. From the
constructive point of view, proofs are abstract mathematical objects
that are *denoted* by suitable expressions in dependent type
theory. In contrast, if we think in terms of the coding trick
described above, then the expressions themselves do not denote
anything interesting. Rather, it is the fact that we can write them
down and check that they are well-typed that ensures that the
proposition in question is true. In other words, the expressions
*themselves* are the proofs.

In the exposition below, we will slip back and forth between these two
ways of talking, at times saying that an expression "constructs" or
"produces" or "returns" a proof of a proposition, and at other times
simply saying that it "is" such a proof. This is similar to the way
that computer scientists occasionally blur the distinction between
syntax and semantics by saying, at times, that a program "computes" a
certain function, and at other times speaking as though the program
"is" the function in question.

In any case, all that really matters is the bottom line. To formally
express a mathematical assertion in the language of dependent type
theory, we need to exhibit a term ``p : Prop``. To *prove* that
assertion, we need to exhibit a term ``t : p``. Lean's task, as a
proof assistant, is to help us to construct such a term, ``t``, and to
verify that it is well-formed and has the correct type.
-->

这个功能让我们可以合理地搭建断言和证明。确定表达式 ``t`` 是 ``p`` 的证明，只需检查 ``t`` 具有类型 ``Proof p``。

可以做一些简化。首先，我们可以通过将 ``Proof p`` 和 ``p`` 本身合并来避免重复地写 ``Proof`` 这个词。换句话说，只要我们有 ``p : Prop``，我们就可以把 ``p`` 解释为一种类型，也就是它的证明类型。然后我们可以把 ``t : p`` 读作 ``t`` 是 ``p`` 的证明。

此外，我们可以在 ``Implies p q`` 和 ``p → q`` 之间来回切换。换句话说，命题 ``p`` 和 ``q`` 之间的含义对应于一个函数，它将 ``p`` 的任何元素接受为 ``q`` 的一个元素。因此，引入连接词 ``Implies`` 是完全多余的：我们可以使用依值类型论中常见的函数空间构造子 ``p → q`` 作为我们的蕴含概念。

这是在构造演算（Calculus of Constructions）中遵循的方法，因此在 Lean 中也是如此。自然演绎证明系统中的蕴含规则与控制函数抽象（abstraction）和应用（application）的规则完全一致，这是*Curry-Howard同构*的一个实例，有时也被称为*命题即类型*。事实上，类型 ``Prop`` 是上一章描述的类型层次结构的最底部 ``Sort 0`` 的语法糖。此外，``Type u`` 也只是 ``Sort (u+1)`` 的语法糖。``Prop`` 有一些特殊的特性，但像其他类型宇宙一样，它在箭头构造子下是封闭的:如果我们有 ``p q : Prop``，那么 ``p → q : Prop``。

至少有两种将命题作为类型来思考的方法。对于那些对逻辑和数学中的构造主义者来说，这是对命题含义的忠实诠释：命题 ``p`` 代表了一种数据类型，即构成证明的数据类型的说明。``p`` 的证明就是正确类型的对象 ``t : p``。

非构造主义者可以把它看作是一种简单的编码技巧。对于每个命题 ``p``，我们关联一个类型，如果 ``p`` 为假，则该类型为空，如果 ``p`` 为真，则有且只有一个元素，比如 ``*``。在后一种情况中，让我们说(与之相关的类型)``p`` 被*占据*（inhabited）。恰好，函数应用和抽象的规则可以方便地帮助我们跟踪 ``Prop`` 的哪些元素是被占据的。所以构造一个元素 ``t : p`` 告诉我们 ``p`` 确实是正确的。你可以把 ``p`` 的占据者想象成「``p`` 为真」的事实。对 ``p → q`` 的证明使用「``p`` 是真的」这个事实来得到「``q`` 是真的」这个事实。

事实上，如果 ``p : Prop`` 是任何命题，那么 Lean 的内核将任意两个元素 ``t1 t2 : p`` 看作定义相等，就像它把 ``(fun x => t) s`` 和 ``t[s/x]`` 看作定义等价。这就是所谓的「证明无关性」（proof irrelevance）。这意味着，即使我们可以把证明 ``t : p`` 当作依值类型论语言中的普通对象，它们除了 ``p`` 是真的这一事实之外，没有其他信息。

我们所建议的思考「命题即类型」范式的两种方式在一个根本性的方面有所不同。从构造的角度看，证明是抽象的数学对象，它被依值类型论中的合适表达式所*表示*。相反，如果我们从上述编码技巧的角度考虑，那么表达式本身并不表示任何有趣的东西。相反，是我们可以写下它们并检查它们是否有良好的类型这一事实确保了有关命题是真的。换句话说，表达式*本身*就是证明。

在下面的论述中，我们将在这两种说话方式之间来回切换，有时说一个表达式「构造」或「产生」或「返回」一个命题的证明，有时则简单地说它「是」这样一个证明。这类似于计算机科学家偶尔会模糊语法和语义之间的区别，有时说一个程序「计算」某个函数，有时又说该程序「是」该函数。

为了用依值类型论的语言正式表达一个数学断言，我们需要展示一个项 ``p : Prop``。为了*证明*该断言，我们需要展示一个项 ``t : p``。Lean 的任务，作为一个证明助手，是帮助我们构造这样一个项 ``t``，并验证它的格式是否良好，类型是否正确。

<!--
Working with Propositions as Types
----------------------------------
-->

## 以「命题即类型」的方式工作

<!--
In the propositions-as-types paradigm, theorems involving only ``→``
can be proved using lambda abstraction and application. In Lean, the
``theorem`` command introduces a new theorem:
-->

在「命题即类型」范式中，只涉及 ``→`` 的定理可以通过 lambda 抽象和应用来证明。在 Lean 中，``theorem`` 命令引入了一个新的定理：

```lean
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
```

<!--
Compare this proof to the expression ``fun x : α => fun y : β => x``
of type ``α → β → α``, where ``α`` and ``β`` are data types.
This describes the function that takes arguments ``x`` and ``y``
of type ``α`` and ``β``, respectively, and returns ``x``.
The proof of ``t1`` has the same form, the only difference being that
``p`` and ``q`` are elements of ``Prop`` rather than ``Type``.
Intuitively, our proof of
``p → q → p`` assumes ``p`` and ``q`` are true, and uses the first
hypothesis (trivially) to establish that the conclusion, ``p``, is
true.

Note that the ``theorem`` command is really a version of the
``def`` command: under the propositions and types
correspondence, proving the theorem ``p → q → p`` is really the same
as defining an element of the associated type. To the kernel type
checker, there is no difference between the two.

There are a few pragmatic differences between definitions and
theorems, however. In normal circumstances, it is never necessary to
unfold the "definition" of a theorem; by proof irrelevance, any two
proofs of that theorem are definitionally equal. Once the proof of a
theorem is complete, typically we only need to know that the proof
exists; it doesn't matter what the proof is. In light of that fact,
Lean tags proofs as *irreducible*, which serves as a hint to the
parser (more precisely, the *elaborator*) that there is generally no
need to unfold it when processing a file. In fact, Lean is generally
able to process and check proofs in parallel, since assessing the
correctness of one proof does not require knowing the details of
another.

As with definitions, the ``#print`` command will show you the proof of
a theorem.
-->

这与上一章中常量函数的定义完全相同，唯一的区别是参数是 ``Prop`` 的元素，而不是 ``Type`` 的元素。直观地说，我们对 ``p → q → p`` 的证明假设 ``p`` 和 ``q`` 为真，并使用第一个假设(平凡地)建立结论 ``p`` 为真。

请注意，``theorem`` 命令实际上是 ``def`` 命令的一个翻版：在命题和类型对应下，证明定理 ``p → q → p`` 实际上与定义关联类型的元素是一样的。对于内核类型检查器，这两者之间没有区别。

然而，定义和定理之间有一些实用的区别。正常情况下，永远没有必要展开一个定理的「定义」；通过证明无关性，该定理的任何两个证明在定义上都是相等的。一旦一个定理的证明完成，通常我们只需要知道该证明的存在；证明是什么并不重要。鉴于这一事实，Lean 将证明标记为*不可还原*（irreducible），作为对解析器（更确切地说，是 **繁饰器** ）的提示，在处理文件时一般不需要展开它。事实上，Lean 通常能够并行地处理和检查证明，因为评估一个证明的正确性不需要知道另一个证明的细节。

和定义一样，``#print`` 命令可以展示一个定理的证明。

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1
```

<!--
Notice that the lambda abstractions ``hp : p`` and ``hq : q`` can be
viewed as temporary assumptions in the proof of ``t1``.  Lean also
allows us to specify the type of the final term ``hp``, explicitly,
with a ``show`` statement.
-->

注意，lambda抽象 ``hp : p`` 和 ``hq : q`` 可以被视为 ``t1`` 的证明中的临时假设。Lean 还允许我们通过 ``show`` 语句明确指定最后一个项 ``hp`` 的类型。

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp
```

<!--
Adding such extra information can improve the clarity of a proof and
help detect errors when writing a proof. The ``show`` command does
nothing more than annotate the type, and, internally, all the
presentations of ``t1`` that we have seen produce the same term.

As with ordinary definitions, we can move the lambda-abstracted
variables to the left of the colon:
-->

添加这些额外的信息可以提高证明的清晰度，并有助于在编写证明时发现错误。``show`` 命令只是注释类型，而且在内部，我们看到的所有关于 ``t1`` 的表示都产生了相同的项。

与普通定义一样，我们可以将 lambda 抽象的变量移到冒号的左边：

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

#print t1    -- p → q → p
```

<!--
Now we can apply the theorem ``t1`` just as a function application.
-->

现在我们可以把定理 ``t1`` 作为一个函数应用。

```lean
# variable {p : Prop}
# variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp
```

<!--
Here, the ``axiom`` declaration postulates the existence of an
element of the given type and may compromise logical consistency. For
example, we can use it to postulate the empty type `False` has an
element.
-->

这里，``axiom`` 声明假定存在给定类型的元素，因此可能会破坏逻辑一致性。例如，我们可以使用它来假设空类型 `False` 有一个元素：

<!--
```lean
axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound
```
-->

```lean
axiom unsound : False
-- false可导出一切
theorem ex : 1 = 0 :=
False.elim unsound
```

<!--
Declaring an "axiom" ``hp : p`` is tantamount to declaring that ``p``
is true, as witnessed by ``hp``. Applying the theorem
``t1 : p → q → p`` to the fact ``hp : p`` that ``p`` is true yields the theorem
``t1 hp : q → p``.

Recall that we can also write theorem ``t1`` as follows:
-->

声明「公理」``hp : p`` 等同于声明 ``p`` 为真，正如 ``hp`` 所证明的那样。应用定理 ``t1 : p → q → p`` 到事实 ``hp : p``（也就是 ``p`` 为真）得到定理 ``t1 hp : q → p``。

回想一下，我们也可以这样写定理 ``t1``:

```lean
theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1
```

<!--
The type of ``t1`` is now ``∀ {p q : Prop}, p → q → p``. We can read
this as the assertion "for every pair of propositions ``p q``, we have
``p → q → p``." For example, we can move all parameters to the right
of the colon:
-->

``t1`` 的类型现在是 ``∀ {p q : Prop}, p → q → p``。我们可以把它理解为「对于每一对命题 ``p q``，我们都有 ``p → q → p``」。例如，我们可以将所有参数移到冒号的右边：

```lean
theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp
```

<!--
If ``p`` and ``q`` have been declared as variables, Lean will
generalize them for us automatically:
-->

如果 ``p`` 和 ``q`` 被声明为变量，Lean 会自动为我们推广它们：

```lean
variable {p q : Prop}

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
```

<!--
In fact, by the propositions-as-types correspondence, we can declare
the assumption ``hp`` that ``p`` holds, as another variable:
-->

事实上，通过命题即类型的对应关系，我们可以声明假设 ``hp`` 为 ``p``，作为另一个变量:

```lean
variable {p q : Prop}
variable (hp : p)

theorem t1 : q → p := fun (hq : q) => hp
```

<!--
Lean detects that the proof uses ``hp`` and automatically adds
``hp : p`` as a premise. In all cases, the command ``#print t1`` still yields
``∀ p q : Prop, p → q → p``. Remember that this type can just as well
be written ``∀ (p q : Prop) (hp : p) (hq : q), p``, since the arrow
denotes nothing more than an arrow type in which the target does not
depend on the bound variable.

When we generalize ``t1`` in such a way, we can then apply it to
different pairs of propositions, to obtain different instances of the
general theorem.
-->

Lean 检测到证明使用 ``hp``，并自动添加 ``hp : p`` 作为前提。在所有情况下，命令 ``#print t1`` 仍然会产生 ``∀ p q : Prop, p → q → p``。这个类型也可以写成 ``∀ (p q : Prop) (hp : p) (hq :q), p``，因为箭头仅仅表示一个箭头类型，其中目标不依赖于约束变量。

当我们以这种方式推广 ``t1`` 时，我们就可以将它应用于不同的命题对，从而得到一般定理的不同实例。

```lean
theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q                -- p → q → p
#check t1 r s                -- r → s → r
#check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1 (r → s) (s → r) h  -- (s → r) → r → s
```

<!--
Once again, using the propositions-as-types correspondence, the
variable ``h`` of type ``r → s`` can be viewed as the hypothesis, or
premise, that ``r → s`` holds.

As another example, let us consider the composition function discussed
in the last chapter, now with propositions instead of types.
-->

同样，使用命题即类型对应，类型为 ``r → s`` 的变量 ``h`` 可以看作是 ``r → s`` 存在的假设或前提。

作为另一个例子，让我们考虑上一章讨论的组合函数，现在用命题代替类型。

```lean
variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
```

<!--
As a theorem of propositional logic, what does ``t2`` say?

Note that it is often useful to use numeric unicode subscripts,
entered as ``\0``, ``\1``, ``\2``, ..., for hypotheses, as we did in
this example.
-->

作为一个命题逻辑定理，``t2`` 是什么意思？

注意，数字 unicode 下标输入方式为 ``\0``，``\1``，``\2``，...。

<!--
Propositional Logic
-------------------
-->

## 命题逻辑

<!--
Lean defines all the standard logical connectives and notation. The propositional connectives come with the following notation:

| Ascii             | Unicode   | Editor shortcut              | Definition   |
|-------------------|-----------|------------------------------|--------------|
| True              |           |                              | True         |
| False             |           |                              | False        |
| Not               | ¬         | ``\not``, ``\neg``           | Not          |
| /\\               | ∧         | ``\and``                     | And          |
| \\/               | ∨         | ``\or``                      | Or           |
| ->                | →         | ``\to``, ``\r``, ``\imp``    |              |
| <->               | ↔         | ``\iff``, ``\lr``            | Iff          |

They all take values in ``Prop``.
-->

Lean 定义了所有标准的逻辑连接词和符号。命题连接词有以下表示法:

| Ascii      | Unicode   | 编辑器缩写                | 定义   |
|------------|-----------|--------------------------|--------|
| True       |           |                          | True   |
| False      |           |                          | False  |
| Not        | ¬         | ``\not``, ``\neg``       | Not    |
| /\\        | ∧        | ``\and``                 | And    |
| \\/        | ∨        | ``\or``                  | Or     |
| ->         | →         | ``\to``, ``\r``, ``\imp``|        |
| <->        | ↔         | ``\iff``, ``\lr``        | Iff    |

它们都接收 ``Prop`` 值。

```lean
variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p
```

<!--
The order of operations is as follows: unary negation ``¬`` binds most
strongly, then ``∧``, then ``∨``, then ``→``, and finally ``↔``. For
example, ``a ∧ b → c ∨ d ∧ e`` means ``(a ∧ b) → (c ∨ (d ∧
e))``. Remember that ``→`` associates to the right (nothing changes
now that the arguments are elements of ``Prop``, instead of some other
``Type``), as do the other binary connectives. So if we have
``p q r : Prop``, the expression ``p → q → r`` reads "if ``p``, then if ``q``,
then ``r``." This is just the "curried" form of ``p ∧ q → r``.

In the last chapter we observed that lambda abstraction can be viewed
as an "introduction rule" for ``→``. In the current setting, it shows
how to "introduce" or establish an implication. Application can be
viewed as an "elimination rule," showing how to "eliminate" or use an
implication in a proof. The other propositional connectives are
defined in Lean's library in the file ``Prelude.core`` (see
[importing files](./interacting_with_lean.md#importing-files) for more information on the library
hierarchy), and each connective comes with its canonical introduction
and elimination rules.
-->

操作符的优先级如下：``¬ > ∧ > ∨ > → > ↔``。举例：``a ∧ b → c ∨ d ∧ e`` 意为 ``(a ∧ b) → (c ∨ (d ∧ e))``。``→`` 等二元关系是右结合的。所以如果我们有 ``p q r : Prop``，表达式 ``p → q → r`` 读作「如果 ``p``，那么如果 ``q``，那么 ``r``」。这是 ``p ∧ q → r`` 的柯里化形式。

在上一章中，我们观察到 lambda 抽象可以被看作是 ``→`` 的「引入规则」，展示了如何「引入」或建立一个蕴含。应用可以看作是一个「消去规则」，展示了如何在证明中「消去」或使用一个蕴含。其他的命题连接词在 Lean 的库 ``Prelude.core`` 文件中定义。(参见[导入文件](./interacting_with_lean.md#_importing_files)以获得关于库层次结构的更多信息)，并且每个连接都带有其规范引入和消去规则。

<!--
### Conjunction
-->

### 合取

<!--
The expression ``And.intro h1 h2`` builds a proof of ``p ∧ q`` using
proofs ``h1 : p`` and ``h2 : q``. It is common to describe
``And.intro`` as the *and-introduction* rule. In the next example we
use ``And.intro`` to create a proof of ``p → q → p ∧ q``.
-->

表达式 ``And.intro h1 h2`` 是 ``p ∧ q`` 的证明，它使用了 ``h1 : p`` 和 ``h2 : q`` 的证明。通常把 ``And.intro`` 称为*合取引入*规则。下面的例子我们使用 ``And.intro`` 来创建 ``p → q → p ∧ q`` 的证明。

```lean
variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq
```

<!--
The ``example`` command states a theorem without naming it or storing
it in the permanent context. Essentially, it just checks that the
given term has the indicated type. It is convenient for illustration,
and we will use it often.

The expression ``And.left h`` creates a proof of ``p`` from a proof
``h : p ∧ q``. Similarly, ``And.right h`` is a proof of ``q``. They
are commonly known as the left and right *and-elimination* rules.
-->

``example`` 命令声明了一个没有名字也不会永久保存的定理。本质上，它只是检查给定项是否具有指定的类型。它便于说明，我们将经常使用它。

表达式 ``And.left h`` 从 ``h : p ∧ q`` 建立了一个 ``p`` 的证明。类似地，``And.right h`` 是 ``q`` 的证明。它们常被称为左或右*合取消去*规则。

```lean
variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
```

<!--
We can now prove ``p ∧ q → q ∧ p`` with the following proof term.
-->

我们现在可以证明 ``p ∧ q → q ∧ p``：

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
```

<!--
Notice that and-introduction and and-elimination are similar to the
pairing and projection operations for the Cartesian product. The
difference is that given ``hp : p`` and ``hq : q``, ``And.intro hp
hq`` has type ``p ∧ q : Prop``, while ``Prod hp hq`` has type
``p × q : Type``. The similarity between ``∧`` and ``×`` is another instance
of the Curry-Howard isomorphism, but in contrast to implication and
the function space constructor, ``∧`` and ``×`` are treated separately
in Lean. With the analogy, however, the proof we have just constructed
is similar to a function that swaps the elements of a pair.

We will see in [Chapter Structures and Records](./structures_and_records.md) that certain
types in Lean are *structures*, which is to say, the type is defined
with a single canonical *constructor* which builds an element of the
type from a sequence of suitable arguments. For every ``p q : Prop``,
``p ∧ q`` is an example: the canonical way to construct an element is
to apply ``And.intro`` to suitable arguments ``hp : p`` and
``hq : q``. Lean allows us to use *anonymous constructor* notation
``⟨arg1, arg2, ...⟩`` in situations like these, when the relevant type is an
inductive type and can be inferred from the context. In particular, we
can often write ``⟨hp, hq⟩`` instead of ``And.intro hp hq``:
-->

请注意，引入和消去与笛卡尔积的配对和投影操作类似。区别在于，给定 ``hp : p`` 和 ``hq : q``，``And.intro hp hq`` 具有类型 ``p ∧ q : Prop``，而 ``Prod hp hq`` 具有类型 ``p × q : Type``。``∧`` 和 ``×`` 之间的相似性是Curry-Howard同构的另一个例子，但与蕴涵和函数空间构造子不同，在 Lean 中 ``∧`` 和 ``×`` 是分开处理的。然而，通过类比，我们刚刚构造的证明类似于交换一对中的元素的函数。

我们将在[结构体和记录](./structures_and_records.md)一章中看到 Lean 中的某些类型是*Structures*，也就是说，该类型是用单个规范的*构造子*定义的，该构造子从一系列合适的参数构建该类型的一个元素。对于每一组 ``p q : Prop``， ``p ∧ q`` 就是一个例子:构造一个元素的规范方法是将 ``And.intro`` 应用于合适的参数 ``hp : p`` 和 ``hq : q``。Lean 允许我们使用*匿名构造子*表示法 ``⟨arg1, arg2, ...⟩`` 在此类情况下，当相关类型是归纳类型并可以从上下文推断时。特别地，我们经常可以写入 ``⟨hp, hq⟩``，而不是 ``And.intro hp hq``:

```lean
variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)
```

<!--
These angle brackets are obtained by typing ``\<`` and ``\>``, respectively.

Lean provides another useful syntactic gadget. Given an expression
``e`` of an inductive type ``Foo`` (possibly applied to some
arguments), the notation ``e.bar`` is shorthand for ``Foo.bar e``.
This provides a convenient way of accessing functions without opening
a namespace.  For example, the following two expressions mean the same
thing:
-->

尖括号可以用 ``\<`` 和 ``\>`` 打出来。

Lean 提供了另一个有用的语法小工具。给定一个归纳类型 ``Foo`` 的表达式 ``e``(可能应用于一些参数)，符号 ``e.bar`` 是 ``Foo.bar e`` 的缩写。这为访问函数提供了一种方便的方式，而无需打开名称空间。例如，下面两个表达的意思是相同的：

```lean
variable (xs : List Nat)

#check List.length xs
#check xs.length
```

<!--
As a result, given ``h : p ∧ q``, we can write ``h.left`` for
``And.left h`` and ``h.right`` for ``And.right h``. We can therefore
rewrite the sample proof above conveniently as follows:
-->

给定 ``h : p ∧ q``，我们可以写 ``h.left`` 来表示 ``And.left h`` 以及 ``h.right`` 来表示 ``And.right h``。因此我们可以简写上面的证明如下：

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩
```

<!--
There is a fine line between brevity and obfuscation, and omitting
information in this way can sometimes make a proof harder to read. But
for straightforward constructions like the one above, when the type of
``h`` and the goal of the construction are salient, the notation is
clean and effective.

It is common to iterate constructions like "And." Lean also allows you
to flatten nested constructors that associate to the right, so that
these two proofs are equivalent:
-->

在简洁和含混不清之间有一条微妙的界限，以这种方式省略信息有时会使证明更难阅读。但对于像上面这样简单的结构，当 ``h`` 的类型和结构的目标很突出时，符号是干净和有效的。

像 ``And.`` 这样的迭代结构是很常见的。Lean 还允许你将嵌套的构造函数向右结合，这样这两个证明是等价的:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩
```

<!--
This is often useful as well.
-->

这一点也很常用。

<!--
### Disjunction
-->

### 析取

<!--
The expression ``Or.intro_left q hp`` creates a proof of ``p ∨ q``
from a proof ``hp : p``. Similarly, ``Or.intro_right p hq`` creates a
proof for ``p ∨ q`` using a proof ``hq : q``. These are the left and
right *or-introduction* rules.
-->

表达式 ``Or.intro_left q hp`` 从证明 ``hp : p`` 建立了 ``p ∨ q`` 的证明。类似地，``Or.intro_right p hq`` 从证明 ``hq : q`` 建立了 ``p ∨ q`` 的证明。这是左右析取（「或」）引入规则。

```lean
variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
```

<!--
The *or-elimination* rule is slightly more complicated. The idea is
that we can prove ``r`` from ``p ∨ q``, by showing that ``r`` follows
from ``p`` and that ``r`` follows from ``q``.  In other words, it is a
proof by cases. In the expression ``Or.elim hpq hpr hqr``, ``Or.elim``
takes three arguments, ``hpq : p ∨ q``, ``hpr : p → r`` and
``hqr : q → r``, and produces a proof of ``r``. In the following example, we use
``Or.elim`` to prove ``p ∨ q → q ∨ p``.
-->

析取消去规则稍微复杂一点。这个想法是，如果我们想要从 ``p ∨ q`` 证明 ``r``，只需要展示 ``p`` 可以证明 ``r``，且 ``q`` 也可以证明 ``r``。换句话说，它是一种逐情况证明。在表达式 ``Or.elim hpq hpr hqr`` 中，``Or.elim`` 接受三个论证，``hpq : p ∨ q``，``hpr : p → r`` 和 ``hqr : q → r``，生成 ``r`` 的证明。在下面的例子中，我们使用 ``Or.elim`` 证明 ``p ∨ q → q ∨ p``。

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)
```

<!--
In most cases, the first argument of ``Or.intro_right`` and
``Or.intro_left`` can be inferred automatically by Lean. Lean
therefore provides ``Or.inr`` and ``Or.inl`` which can be viewed as
shorthand for ``Or.intro_right _`` and ``Or.intro_left _``. Thus the
proof term above could be written more concisely:
-->

在大多数情况下，``Or.intro_right`` 和 ``Or.intro_left`` 的第一个参数可以由 Lean 自动推断出来。因此，Lean 提供了 ``Or.inr`` 和 ``Or.inl`` 作为 ``Or.intro_right _`` 和 ``Or.intro_left _`` 的缩写。因此，上面的证明项可以写得更简洁:

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

<!--
Notice that there is enough information in the full expression for
Lean to infer the types of ``hp`` and ``hq`` as well.  But using the
type annotations in the longer version makes the proof more readable,
and can help catch and debug errors.

Because ``Or`` has two constructors, we cannot use anonymous
constructor notation. But we can still write ``h.elim`` instead of
``Or.elim h``:
-->

Lean 的完整表达式中有足够的信息来推断 ``hp`` 和 ``hq`` 的类型。但是在较长的版本中使用类型注释可以使证明更具可读性，并有助于捕获和调试错误。

因为 ``Or`` 有两个构造子，所以不能使用匿名构造子表示法。但我们仍然可以写 ``h.elim`` 而不是 ``Or.elim h``，不过你需要注意这些缩写是增强还是降低了可读性：

```lean
variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
```

<!--
Once again, you should exercise judgment as to whether such
abbreviations enhance or diminish readability.
-->

<!--
### Negation and Falsity
-->

### 否定和假言

<!--
Negation, ``¬p``, is actually defined to be ``p → False``, so we
obtain ``¬p`` by deriving a contradiction from ``p``. Similarly, the
expression ``hnp hp`` produces a proof of ``False`` from ``hp : p``
and ``hnp : ¬p``. The next example uses both these rules to produce a
proof of ``(p → q) → ¬q → ¬p``. (The symbol ``¬`` is produced by
typing ``\not`` or ``\neg``.)
-->

否定 ``¬p`` 真正的定义是 ``p → False``，所以我们通过从 ``p`` 导出一个矛盾来获得 ``¬p``。类似地，表达式 ``hnp hp`` 从 ``hp : p`` 和 ``hnp : ¬p`` 产生一个 ``False`` 的证明。下一个例子用所有这些规则来证明 ``(p → q) → ¬q → ¬p``。（``¬`` 符号可以由 ``\not`` 或者 ``\neg`` 来写出。）

```lean
variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)
```

<!--
The connective ``False`` has a single elimination rule,
``False.elim``, which expresses the fact that anything follows from a
contradiction. This rule is sometimes called *ex falso* (short for *ex
falso sequitur quodlibet*), or the *principle of explosion*.
-->

连接词 ``False`` 只有一个消去规则 ``False.elim``，它表达了一个事实，即矛盾能导出一切。这个规则有时被称为*ex falso* 【*ex falso sequitur quodlibet*（无稽之谈）的缩写】，或*爆炸原理*。

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
```

<!--
The arbitrary fact, ``q``, that follows from falsity is an implicit
argument in ``False.elim`` and is inferred automatically. This
pattern, deriving an arbitrary fact from contradictory hypotheses, is
quite common, and is represented by ``absurd``.
-->

假命题导出任意的事实 ``q``，是 ``False.elim`` 的一个隐参数，而且是自动推断出来的。这种从相互矛盾的假设中推导出任意事实的模式很常见，用 ``absurd`` 来表示。

```lean
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp
```

<!--
Here, for example, is a proof of ``¬p → q → (q → p) → r``:
-->

证明 ``¬p → q → (q → p) → r``：

```lean
variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
```

<!--
Incidentally, just as ``False`` has only an elimination rule, ``True``
has only an introduction rule, ``True.intro : true``.  In other words,
``True`` is simply true, and has a canonical proof, ``True.intro``.
-->

顺便说一句，就像 ``False`` 只有一个消去规则，``True`` 只有一个引入规则 ``True.intro : true``。换句话说，``True`` 就是真，并且有一个标准证明 ``True.intro``。

<!--
### Logical Equivalence
-->

### 逻辑等价

<!--
The expression ``Iff.intro h1 h2`` produces a proof of ``p ↔ q`` from
``h1 : p → q`` and ``h2 : q → p``.  The expression ``Iff.mp h``
produces a proof of ``p → q`` from ``h : p ↔ q``. Similarly,
``Iff.mpr h`` produces a proof of ``q → p`` from ``h : p ↔ q``. Here is a proof
of ``p ∧ q ↔ q ∧ p``:
-->

表达式 ``Iff.intro h1 h2`` 从 ``h1 : p → q`` 和 ``h2 : q → p`` 生成了 ``p ↔ q`` 的证明。表达式 ``Iff.mp h`` 从 ``h : p ↔ q`` 生成了 ``p → q`` 的证明。表达式 ``Iff.mpr h`` 从 ``h : p ↔ q`` 生成了 ``q → p`` 的证明。下面是 ``p ∧ q ↔ q ∧ p`` 的证明：

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h
```

<!--
We can use the anonymous constructor notation to construct a proof of
``p ↔ q`` from proofs of the forward and backward directions, and we
can also use ``.`` notation with ``mp`` and ``mpr``. The previous
examples can therefore be written concisely as follows:
-->

我们可以用匿名构造子表示法来，从正反两个方向的证明，来构建 ``p ↔ q`` 的证明。我们也可以使用 ``.`` 符号连接 ``mp`` 和 ``mpr``。因此，前面的例子可以简写如下：

```lean
variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
```

<!--
Introducing Auxiliary Subgoals
--------
-->

## 引入辅助 子目标

<!--
This is a good place to introduce another device Lean offers to help
structure long proofs, namely, the ``have`` construct, which
introduces an auxiliary subgoal in a proof. Here is a small example,
adapted from the last section:
-->

这里介绍 Lean 提供的另一种帮助构造长证明的方法，即 ``have`` 结构，它在证明中引入了一个辅助的子目标。下面是一个小例子，改编自上一节:

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
```

<!--
Internally, the expression ``have h : p := s; t`` produces the term
``(fun (h : p) => t) s``. In other words, ``s`` is a proof of ``p``,
``t`` is a proof of the desired conclusion assuming ``h : p``, and the
two are combined by a lambda abstraction and application. This simple
device is extremely useful when it comes to structuring long proofs,
since we can use intermediate ``have``'s as stepping stones leading to
the final goal.

Lean also supports a structured way of reasoning backwards from a
goal, which models the "suffices to show" construction in ordinary
mathematics. The next example simply permutes the last two lines in
the previous proof.
-->

在内部，表达式 ``have h : p := s; t`` 产生项 ``(fun (h : p) => t) s``。换句话说，``s`` 是 ``p`` 的证明，``t`` 是假设 ``h : p`` 的期望结论的证明，并且这两个是由 lambda 抽象和应用组合在一起的。这个简单的方法在构建长证明时非常有用，因为我们可以使用中间的 ``have`` 作为通向最终目标的垫脚石。

Lean 还支持从目标向后推理的结构化方法，它模仿了普通数学文献中「足以说明某某」（suffices to show）的构造。下一个例子简单地排列了前面证明中的最后两行。

```lean
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
```

<!--
Writing ``suffices hq : q`` leaves us with two goals. First, we have
to show that it indeed suffices to show ``q``, by proving the original
goal of ``q ∧ p`` with the additional hypothesis ``hq : q``. Finally,
we have to show ``q``.
-->

``suffices hq : q`` 给出了两条目标。第一，我们需要证明，通过利用附加假设 ``hq : q`` 证明原目标 ``q ∧ p``，这样足以证明 ``q``，第二，我们需要证明 ``q``。

<!--
Classical Logic
---------------
-->

## 经典逻辑

<!--
The introduction and elimination rules we have seen so far are all
constructive, which is to say, they reflect a computational
understanding of the logical connectives based on the
propositions-as-types correspondence. Ordinary classical logic adds to
this the law of the excluded middle, ``p ∨ ¬p``. To use this
principle, you have to open the classical namespace.
-->

到目前为止，我们看到的引入和消去规则都是构造主义的，也就是说，它们反映了基于命题即类型对应的逻辑连接词的计算理解。普通经典逻辑在此基础上加上了排中律 ``p ∨ ¬p``（excluded middle, em）。要使用这个原则，你必须打开经典逻辑命名空间。

```lean
open Classical

variable (p : Prop)
#check em p
```

<!--
Intuitively, the constructive "Or" is very strong: asserting ``p ∨ q``
amounts to knowing which is the case. If ``RH`` represents the Riemann
hypothesis, a classical mathematician is willing to assert
``RH ∨ ¬RH``, even though we cannot yet assert either disjunct.

One consequence of the law of the excluded middle is the principle of
double-negation elimination:
-->

从直觉上看，构造主义的「或」非常强：断言 ``p ∨ q`` 等于知道哪个是真实情况。如果 ``RH`` 代表黎曼猜想，经典数学家愿意断言 ``RH ∨ ¬RH``，即使我们还不能断言析取式的任何一端。

排中律的一个结果是双重否定消去规则（double-negation elimination, dne）:

```lean
open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)
```

<!--
Double-negation elimination allows one to prove any proposition,
``p``, by assuming ``¬p`` and deriving ``false``, because that amounts
to proving ``¬¬p``. In other words, double-negation elimination allows
one to carry out a proof by contradiction, something which is not
generally possible in constructive logic. As an exercise, you might
try proving the converse, that is, showing that ``em`` can be proved
from ``dne``.

The classical axioms also give you access to additional patterns of
proof that can be justified by appeal to ``em``.  For example, one can
carry out a proof by cases:
-->

双重否定消去规则给出了一种证明任何命题 ``p`` 的方法：通过假设 ``¬p`` 来推导出 ``false``，相当于证明了 ``p``。换句话说，双重否定消除允许反证法，这在构造主义逻辑中通常是不可能的。作为练习，你可以试着证明相反的情况，也就是说，证明 ``em`` 可以由 ``dne`` 证明。

经典公理还可以通过使用 ``em`` 让你获得额外的证明模式。例如，我们可以逐情况进行证明:

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)
```

<!--
Or you can carry out a proof by contradiction:
-->

或者你可以用反证法来证明：

```lean
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)
```

<!--
If you are not used to thinking constructively, it may take some time
for you to get a sense of where classical reasoning is used.  It is
needed in the following example because, from a constructive
standpoint, knowing that ``p`` and ``q`` are not both true does not
necessarily tell you which one is false:
-->

如果你不习惯构造主义，你可能需要一些时间来了解经典推理在哪里使用。在下面的例子中，它是必要的，因为从一个构造主义的观点来看，知道 ``p`` 和 ``q`` 不同时真并不一定告诉你哪一个是假的：

```lean
# open Classical
# variable (p q : Prop)
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)
```
<!--

We will see later that there *are* situations in constructive logic
where principles like excluded middle and double-negation elimination
are permissible, and Lean supports the use of classical reasoning in
such contexts without relying on excluded middle.

The full list of axioms that are used in Lean to support classical
reasoning are discussed in [Axioms and Computation](./axioms_and_computation.md).
-->


稍后我们将看到，构造逻辑中 **有** 某些情况允许「排中律」和「双重否定消除律」等，而 Lean 支持在这种情况下使用经典推理，而不依赖于排中律。

Lean 中使用的公理的完整列表见[公理与计算](./axioms_and_computation.md)。

<!--
Examples of Propositional Validities
------------------------------------
-->

逻辑命题的例子

<!--
Lean's standard library contains proofs of many valid statements of
propositional logic, all of which you are free to use in proofs of
your own. The following list includes a number of common identities.
-->

Lean 的标准库包含了许多命题逻辑的有效语句的证明，你可以自由地在自己的证明中使用这些证明。下面的列表包括一些常见的逻辑等价式。

<!--
Commutativity:
-->

交换律：

1. ``p ∧ q ↔ q ∧ p``
2. ``p ∨ q ↔ q ∨ p``

<!--
Associativity:
-->

结合律：

3. ``(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)``
4. ``(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)``

<!--
Distributivity:
-->

分配律：

5. ``p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)``
6. ``p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)``

<!--
Other properties:
-->

其他性质：

7. ``(p → (q → r)) ↔ (p ∧ q → r)``
8. ``((p ∨ q) → r) ↔ (p → r) ∧ (q → r)``
9. ``¬(p ∨ q) ↔ ¬p ∧ ¬q``
10. ``¬p ∨ ¬q → ¬(p ∧ q)``
11. ``¬(p ∧ ¬p)``
12. ``p ∧ ¬q → ¬(p → q)``
13. ``¬p → (p → q)``
14. ``(¬p ∨ q) → (p → q)``
15. ``p ∨ False ↔ p``
16. ``p ∧ False ↔ False``
17. ``¬(p ↔ ¬p)``
18. ``(p → q) → (¬q → ¬p)``

<!--
These require classical reasoning:
-->

经典推理：

19. ``(p → r ∨ s) → ((p → r) ∨ (p → s))``
20. ``¬(p ∧ q) → ¬p ∨ ¬q``
21. ``¬(p → q) → p ∧ ¬q``
22. ``(p → q) → (¬p ∨ q)``
23. ``(¬q → ¬p) → (p → q)``
24. ``p ∨ ¬p``
25. ``(((p → q) → p) → p)``

<!--
The ``sorry`` identifier magically produces a proof of anything, or
provides an object of any data type at all. Of course, it is unsound
as a proof method -- for example, you can use it to prove ``False`` --
and Lean produces severe warnings when files use or import theorems
which depend on it. But it is very useful for building long proofs
incrementally. Start writing the proof from the top down, using
``sorry`` to fill in subproofs. Make sure Lean accepts the term with
all the ``sorry``'s; if not, there are errors that you need to
correct. Then go back and replace each ``sorry`` with an actual proof,
until no more remain.

Here is another useful trick. Instead of using ``sorry``, you can use
an underscore ``_`` as a placeholder. Recall this tells Lean that
the argument is implicit, and should be filled in automatically. If
Lean tries to do so and fails, it returns with an error message "don't
know how to synthesize placeholder," followed by the type of
the term it is expecting, and all the objects and hypotheses available
in the context. In other words, for each unresolved placeholder, Lean
reports the subgoal that needs to be filled at that point. You can
then construct a proof by incrementally filling in these placeholders.

For reference, here are two sample proofs of validities taken from the
list above.
-->

``sorry`` 标识符神奇地生成任何东西的证明，或者提供任何数据类型的对象。当然，作为一种证明方法，它是不可靠的——例如，你可以使用它来证明 ``False``——并且当文件使用或导入依赖于它的定理时，Lean 会产生严重的警告。但它对于增量地构建长证明非常有用。从上到下写证明，用 ``sorry`` 来填子证明。确保 Lean 接受所有的 ``sorry``；如果不是，则有一些错误需要纠正。然后返回，用实际的证据替换每个 ``sorry``，直到做完。

有另一个有用的技巧。你可以使用下划线 ``_`` 作为占位符，而不是 ``sorry``。回想一下，这告诉 Lean 该参数是隐式的，应该自动填充。如果 Lean 尝试这样做并失败了，它将返回一条错误消息「不知道如何合成占位符」（Don't know how to synthesize placeholder），然后是它所期望的项的类型，以及上下文中可用的所有对象和假设。换句话说，对于每个未解决的占位符，Lean 报告在那一点上需要填充的子目标。然后，你可以通过递增填充这些占位符来构造一个证明。

这里有两个简单的证明例子作为参考。

<!--
```lean
open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
```
-->

```lean
open Classical

-- 分配律
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- 需要一点经典推理的例子
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
```

<!--
Exercises
---------
-->

## 练习

<!--
Prove the following identities, replacing the "sorry" placeholders with actual proofs.
-->

证明以下等式，用真实证明取代「sorry」占位符。

<!--
```lean
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
```
-->

```lean
variable (p q r : Prop)

--  ∧ 和 ∨ 的交换律
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- ∧ 和 ∨ 的结合律
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- 分配律
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- 其他性质
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
```

<!--
Prove the following identities, replacing the "sorry" placeholders
with actual proofs. These require classical reasoning.
-->

下面这些需要一点经典逻辑。

```lean
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
```

<!--
Prove ``¬(p ↔ ¬p)`` without using classical logic.
-->

最后，证明 ``¬(p ↔ ¬p)`` 且不使用经典逻辑。
