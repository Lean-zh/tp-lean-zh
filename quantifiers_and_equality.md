<!--
Quantifiers and Equality
========================
-->

量词与等价
========================

<!--
The last chapter introduced you to methods that construct proofs of
statements involving the propositional connectives. In this chapter,
we extend the repertoire of logical constructions to include the
universal and existential quantifiers, and the equality relation.
-->

上一章介绍了构造包含命题连接词的证明方法。在本章中，我们扩展逻辑结构，包括全称量词和存在量词，以及等价关系。

<!--
The Universal Quantifier
------------------------
-->

全称量词
------------------------

<!--
Notice that if ``α`` is any type, we can represent a unary predicate
``p`` on ``α`` as an object of type ``α → Prop``. In that case, given
``x : α``, ``p x`` denotes the assertion that ``p`` holds of
``x``. Similarly, an object ``r : α → α → Prop`` denotes a binary
relation on ``α``: given ``x y : α``, ``r x y`` denotes the assertion
that ``x`` is related to ``y``.

The universal quantifier, ``∀ x : α, p x`` is supposed to denote the
assertion that "for every ``x : α``, ``p x``" holds. As with the
propositional connectives, in systems of natural deduction, "forall"
is governed by an introduction and elimination rule. Informally, the
introduction rule states:

> Given a proof of ``p x``, in a context where ``x : α`` is arbitrary, we obtain a proof ``∀ x : α, p x``.

The elimination rule states:

> Given a proof ``∀ x : α, p x`` and any term ``t : α``, we obtain a proof of ``p t``.

As was the case for implication, the propositions-as-types
interpretation now comes into play. Remember the introduction and
elimination rules for dependent arrow types:

> Given a term ``t`` of type ``β x``, in a context where ``x : α`` is arbitrary, we have ``(fun x : α => t) : (x : α) → β x``.

The elimination rule states:

> Given a term ``s : (x : α) → β x`` and any term ``t : α``, we have ``s t : β t``.

In the case where ``p x`` has type ``Prop``, if we replace
``(x : α) → β x`` with ``∀ x : α, p x``, we can read these as the correct rules
for building proofs involving the universal quantifier.

The Calculus of Constructions therefore identifies dependent arrow
types with forall-expressions in this way. If ``p`` is any expression,
``∀ x : α, p`` is nothing more than alternative notation for
``(x : α) → p``, with the idea that the former is more natural than the latter
in cases where ``p`` is a proposition. Typically, the expression ``p``
will depend on ``x : α``. Recall that, in the case of ordinary
function spaces, we could interpret ``α → β`` as the special case of
``(x : α) → β`` in which ``β`` does not depend on ``x``. Similarly, we
can think of an implication ``p → q`` between propositions as the
special case of ``∀ x : p, q`` in which the expression ``q`` does not
depend on ``x``.

Here is an example of how the propositions-as-types correspondence gets put into practice.
-->

如果 ``α`` 是任何类型，我们可以将 ``α`` 上的一元谓词 ``p`` 作为 ``α → Prop`` 类型的对象。在这种情况下，给定 ``x : α``， ``p x`` 表示断言 ``p`` 在 ``x`` 上成立。类似地，一个对象 ``r : α → α → Prop`` 表示 ``α`` 上的二元关系：给定 ``x y : α``，``r x y`` 表示断言 ``x`` 与 ``y`` 相关。

全称量词 ``∀ x : α, p x`` 表示，对于每一个 ``x : α``，``p x`` 成立。与命题连接词一样，在自然演绎系统中，「forall」有引入和消去规则。非正式地，引入规则是：

> 给定 ``p x`` 的证明，在 ``x : α`` 是任意的情况下，我们得到 ``∀ x : α, p x`` 的证明。

消去规则是：

> 给定 ``∀ x : α, p x`` 的证明和任何项 ``t : α``，我们得到 ``p t`` 的证明。

与蕴含的情况一样，命题即类型。回想依值箭头类型的引入规则:

> 给定类型为 ``β x`` 的项 ``t``，在 ``x : α`` 是任意的情况下，我们有 ``(fun x : α => t) : (x : α) → β x``。

消去规则：

> 给定项 ``s : (x : α) → β x`` 和任何项 ``t : α``，我们有 ``s t : β t``。

在 ``p x`` 具有 ``Prop`` 类型的情况下，如果我们用 ``∀ x : α, p x`` 替换 ``(x : α) → β x``，就得到构建涉及全称量词的证明的规则。

因此，构造演算用全称表达式来识别依值箭头类型。如果 ``p`` 是任何表达式，``∀ x : α, p`` 不过是 ``(x : α) → p`` 的替代符号，在 ``p`` 是命题的情况下，前者比后者更自然。通常，表达式 ``p`` 取决于 ``x : α``。回想一下，在普通函数空间中，我们可以将 ``α → β`` 解释为 ``(x : α) → β`` 的特殊情况，其中 ``β`` 不依赖于 ``x``。类似地，我们可以把命题之间的蕴涵 ``p → q`` 看作是 ``∀ x : p, q`` 的特殊情况，其中 ``q`` 不依赖于 ``x``。

下面是一个例子，说明了如何运用命题即类型对应规则。``∀`` 可以用 ``\forall`` 输入，也可以用前两个字母简写 ``\fo``。

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left
```

<!--
As a notational convention, we give the universal quantifier the
widest scope possible, so parentheses are needed to limit the
quantifier over ``x`` to the hypothesis in the example above. The
canonical way to prove ``∀ y : α, p y`` is to take an arbitrary ``y``,
and prove ``p y``. This is the introduction rule. Now, given that
``h`` has type ``∀ x : α, p x ∧ q x``, the expression ``h y`` has type
``p y ∧ q y``. This is the elimination rule. Taking the left conjunct
gives the desired conclusion, ``p y``.

Remember that expressions which differ up to renaming of bound
variables are considered to be equivalent. So, for example, we could
have used the same variable, ``x``, in both the hypothesis and
conclusion, and instantiated it by a different variable, ``z``, in the
proof:
-->

作为一种符号约定，我们给予全称量词尽可能最宽的优先级范围，因此上面例子中的假设中，需要用括号将 ``x`` 上的量词限制起来。证明 ``∀ y : α, p y`` 的标准方法是取任意的 ``y``，然后证明 ``p y``。这是引入规则。现在，给定 ``h`` 有类型 ``∀ x : α, p x ∧ q x``，表达式 ``h y`` 有类型 ``p y ∧ q y``。这是消去规则。取合取的左侧得到想要的结论 ``p y``。

只有约束变量名称不同的表达式被认为是等价的。因此，例如，我们可以在假设和结论中使用相同的变量 ``x``，并在证明中用不同的变量 ``z`` 实例化它:

```lean
example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)
```

<!--
As another example, here is how we can express the fact that a relation, ``r``, is transitive:
-->

再举一个例子，下面是关系 ``r`` 的传递性：

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c -- r a b → r b c → r a c
#check trans_r a b c hab -- r b c → r a c
#check trans_r a b c hab hbc -- r a c
```
<!--

Think about what is going on here. When we instantiate ``trans_r`` at
the values ``a b c``, we end up with a proof of ``r a b → r b c → r a c``.
Applying this to the "hypothesis" ``hab : r a b``, we get a proof
of the implication ``r b c → r a c``. Finally, applying it to the
hypothesis ``hbc`` yields a proof of the conclusion ``r a c``.

In situations like this, it can be tedious to supply the arguments
``a b c``, when they can be inferred from ``hab hbc``. For that reason, it
is common to make these arguments implicit:
-->

当我们在值 ``a b c`` 上实例化 ``trans_r`` 时，我们最终得到 ``r a b → r b c → r a c`` 的证明。将此应用于「假设」``hab : r a b``，我们得到了 ``r b c → r a c`` 的一个证明。最后将它应用到假设 ``hbc`` 中，得到结论 ``r a c`` 的证明。

```lean
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc
```

<!--
The advantage is that we can simply write ``trans_r hab hbc`` as a
proof of ``r a c``. A disadvantage is that Lean does not have enough
information to infer the types of the arguments in the expressions
``trans_r`` and ``trans_r hab``. The output of the first ``#check``
command is ``r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3``, indicating
that the implicit arguments are unspecified in this case.

Here is an example of how we can carry out elementary reasoning with an equivalence relation:
-->

优点是我们可以简单地写 ``trans_r hab hbc`` 作为 ``r a c`` 的证明。一个缺点是 Lean 没有足够的信息来推断表达式 ``trans_r`` 和 ``trans_r hab`` 中的参数类型。第一个 ``#check`` 命令的输出是 ``r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3``，表示在本例中隐式参数未指定。

下面是一个用等价关系进行基本推理的例子:

```lean
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd
```

<!--
To get used to using universal quantifiers, you should try some of the
exercises at the end of this section.

It is the typing rule for dependent arrow types, and the universal
quantifier in particular, that distinguishes ``Prop`` from other
types.  Suppose we have ``α : Sort i`` and ``β : Sort j``, where the
expression ``β`` may depend on a variable ``x : α``. Then
``(x : α) → β`` is an element of ``Sort (imax i j)``, where ``imax i j`` is the
maximum of ``i`` and ``j`` if ``j`` is not 0, and 0 otherwise.

The idea is as follows. If ``j`` is not ``0``, then ``(x : α) → β`` is
an element of ``Sort (max i j)``. In other words, the type of
dependent functions from ``α`` to ``β`` "lives" in the universe whose
index is the maximum of ``i`` and ``j``. Suppose, however, that ``β``
is of ``Sort 0``, that is, an element of ``Prop``. In that case,
``(x : α) → β`` is an element of ``Sort 0`` as well, no matter which
type universe ``α`` lives in. In other words, if ``β`` is a
proposition depending on ``α``, then ``∀ x : α, β`` is again a
proposition. This reflects the interpretation of ``Prop`` as the type
of propositions rather than data, and it is what makes ``Prop``
*impredicative*.

The term "predicative" stems from foundational developments around the
turn of the twentieth century, when logicians such as Poincaré and
Russell blamed set-theoretic paradoxes on the "vicious circles" that
arise when we define a property by quantifying over a collection that
includes the very property being defined. Notice that if ``α`` is any
type, we can form the type ``α → Prop`` of all predicates on ``α``
(the "power type of ``α``"). The impredicativity of ``Prop`` means that we
can form propositions that quantify over ``α → Prop``. In particular,
we can define predicates on ``α`` by quantifying over all predicates
on ``α``, which is exactly the type of circularity that was once
considered problematic.
-->

为了习惯使用全称量词，你应该尝试本节末尾的一些练习。

依值箭头类型的类型规则，特别是全称量词，体现了 ``Prop`` 命题类型与其他对象的类型的不同。假设我们有 ``α : Sort i`` 和 ``β : Sort j``，其中表达式 ``β`` 可能依赖于变量 ``x : α``。那么 ``(x : α) → β`` 是 ``Sort (imax i j)`` 的一个元素，其中 ``imax i j`` 是 ``i`` 和 ``j`` 在 ``j`` 不为0时的最大值，否则为0。

其想法如下。如果 ``j`` 不是 ``0``，然后 ``(x : α) → β`` 是 ``Sort (max i j)`` 类型的一个元素。换句话说，从 ``α`` 到 ``β`` 的一类依值函数存在于指数为 ``i`` 和 ``j`` 最大值的宇宙中。然而，假设 ``β`` 属于 ``Sort 0``，即 ``Prop`` 的一个元素。在这种情况下，``(x : α) → β`` 也是 ``Sort 0`` 的一个元素，无论 ``α`` 生活在哪种类型的宇宙中。换句话说，如果 ``β`` 是一个依赖于 ``α`` 的命题，那么 ``∀ x : α, β`` 又是一个命题。这反映出 ``Prop`` 作为一种命题类型而不是数据类型，这也使得 ``Prop`` 具有「非直谓性」（impredicative）。

「直谓性」一词起源于20世纪初的数学基础发展，当时逻辑学家如庞加莱和罗素将集合论的悖论归咎于「恶性循环」：当我们通过量化一个集合来定义一个属性时，这个集合包含了被定义的属性。注意，如果 ``α`` 是任何类型，我们可以在 ``α`` 上形成所有谓词的类型 ``α → Prop``(``α`` 的「幂」类型)。Prop的非直谓性意味着我们可以通过 ``α → Prop`` 形成量化命题。特别是，我们可以通过量化所有关于 ``α`` 的谓词来定义 ``α`` 上的谓词，这正是曾经被认为有问题的循环类型。

<!--
Equality
--------
-->

等价
--------

<!--
Let us now turn to one of the most fundamental relations defined in
Lean's library, namely, the equality relation. In [Chapter Inductive Types](inductive_types.md),
we will explain *how* equality is defined from the primitives of Lean's logical framework.
In the meanwhile, here we explain how to use it.

Of course, a fundamental property of equality is that it is an equivalence relation:
-->

现在让我们来看看在 Lean 库中定义的最基本的关系之一，即等价关系。在[归纳类型](inductive_types.md)一章中，我们将解释如何从 Lean 的逻辑框架中定义等价。在这里我们解释如何使用它。

等价关系的基本性质：反身性、对称性、传递性。

```lean
#check Eq.refl    -- Eq.refl.{u_1} {α : Sort u_1} (a : α) : a = a
#check Eq.symm    -- Eq.symm.{u} {α : Sort u} {a b : α} (h : a = b) : b = a
#check Eq.trans   -- Eq.trans.{u} {α : Sort u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c
```

<!--
We can make the output easier to read by telling Lean not to insert
the implicit arguments (which are displayed here as metavariables).
-->

通过告诉 Lean 不要插入隐参数(在这里显示为元变量)可以使输出更容易阅读。

```lean
universe u

#check @Eq.refl.{u}   -- @Eq.refl : ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- @Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- @Eq.trans : ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
```

<!--
The inscription ``.{u}`` tells Lean to instantiate the constants at the universe ``u``.

Thus, for example, we can specialize the example from the previous section to the equality relation:
-->

``.{u}`` 告诉 Lean 实例化宇宙 ``u`` 上的常量。

因此，我们可以将上一节中的示例具体化为等价关系:

```lean
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```

<!--
We can also use the projection notation:
-->

我们也可以使用投影记号：

```lean
# variable (α : Type) (a b c d : α)
# variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d := (hab.trans hcb.symm).trans hcd
```

<!--
Reflexivity is more powerful than it looks. Recall that terms in the
Calculus of Constructions have a computational interpretation, and
that the logical framework treats terms with a common reduct as the
same. As a result, some nontrivial identities can be proved by
reflexivity:
-->

反身性比它看上去更强大。回想一下，在构造演算中，项有一个计算解释，可规约为相同形式的项会被逻辑框架视为相同的。因此，一些非平凡的恒等式可以通过自反性来证明：

```lean
variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _
```

<!--
This feature of the framework is so important that the library defines a notation ``rfl`` for ``Eq.refl _``:
-->

这个特性非常重要，以至于库中为 ``Eq.refl _`` 专门定义了一个符号 ``rfl``：

```lean
# variable (α β : Type)
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl
```

<!--
Equality is much more than an equivalence relation, however. It has
the important property that every assertion respects the equivalence,
in the sense that we can substitute equal expressions without changing
the truth value. That is, given ``h1 : a = b`` and ``h2 : p a``, we
can construct a proof for ``p b`` using substitution:
``Eq.subst h1 h2``.
-->

然而，等价不仅仅是一种关系。它有一个重要的性质，即每个断言都遵从等价性，即我们可以在不改变真值的情况下对表达式做等价代换。也就是说，给定 ``h1 : a = b`` 和 ``h2 : p a``，我们可以构造一个证明 ``p b``，只需要使用代换 ``Eq.subst h1 h2``。

```lean
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```

<!--
The triangle in the second presentation is a macro built on top of
``Eq.subst`` and ``Eq.symm``, and you can enter it by typing ``\t``.

The rule ``Eq.subst`` is used to define the following auxiliary rules,
which carry out more explicit substitutions. They are designed to deal
with applicative terms, that is, terms of form ``s t``. Specifically,
``congrArg`` can be used to replace the argument, ``congrFun`` can be
used to replace the term that is being applied, and ``congr`` can be
used to replace both at once.
-->

第二个例子中的三角形是建立在 ``Eq.subst`` 和 ``Eq.symm`` 之上的宏，它可以通过 ``\t`` 来输入。

规则 ``Eq.subst`` 定义了一些辅助规则，用来执行更显式的替换。它们是为处理应用型项，即形式为 ``s t`` 的项而设计的。这些辅助规则是，使用 ``congrArg`` 来替换参数，使用 ``congrFun`` 来替换正在应用的项，并且可以同时使用 ``congr`` 来替换两者。

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

<!--
Lean's library contains a large number of common identities, such as these:
-->

Lean 的库包含大量通用的等式，例如：

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

<!--
Note that ``Nat.mul_add`` and ``Nat.add_mul`` are alternative names
for ``Nat.left_distrib`` and ``Nat.right_distrib``, respectively.  The
properties above are stated for the natural numbers (type ``Nat``).

Here is an example of a calculation in the natural numbers that uses
substitution combined with associativity and distributivity.
-->

``Nat.mul_add`` 和 ``Nat.add_mul`` 是 ``Nat.left_distrib`` 和 ``Nat.right_distrib`` 的代称。上面的属性是为自然数类型 ``Nat`` 声明的。

这是一个使用代换以及结合律、交换律和分配律的自然数计算的例子。

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
```

<!--
Notice that the second implicit parameter to ``Eq.subst``, which
provides the context in which the substitution is to occur, has type
``α → Prop``.  Inferring this predicate therefore requires an instance
of *higher-order unification*. In full generality, the problem of
determining whether a higher-order unifier exists is undecidable, and
Lean can at best provide imperfect and approximate solutions to the
problem. As a result, ``Eq.subst`` doesn't always do what you want it
to.  The macro ``h ▸ e`` uses more effective heuristics for computing
this implicit parameter, and often succeeds in situations where
applying ``Eq.subst`` fails.

Because equational reasoning is so common and important, Lean provides
a number of mechanisms to carry it out more effectively. The next
section offers syntax that allow you to write calculational proofs in
a more natural and perspicuous way. But, more importantly, equational
reasoning is supported by a term rewriter, a simplifier, and other
kinds of automation. The term rewriter and simplifier are described
briefly in the next section, and then in greater detail in the next
chapter.
-->

注意，``Eq.subst`` 的第二个隐式参数提供了将要发生代换的表达式上下文，其类型为 ``α → Prop``。因此，推断这个谓词需要一个*高阶合一*（higher-order unification）的实例。一般来说，确定高阶合一器是否存在的问题是无法确定的，而 Lean 充其量只能提供不完美的和近似的解决方案。因此，``Eq.subst`` 并不总是做你想要它做的事。宏 ``h ▸ e`` 使用了更有效的启发式方法来计算这个隐参数，并且在不能应用 ``Eq.subst`` 的情况下通常会成功。

因为等式推理是如此普遍和重要，Lean 提供了许多机制来更有效地执行它。下一节将提供允许你以更自然和清晰的方式编写计算式证明的语法。但更重要的是，等式推理是由项重写器、简化器和其他种类的自动化方法支持的。术语重写器和简化器将在下一节中简要描述，然后在下一章中更详细地描述。

<!--
Calculational Proofs
--------------------
-->

计算式证明
--------------------

<!--
A calculational proof is just a chain of intermediate results that are
meant to be composed by basic principles such as the transitivity of
equality. In Lean, a calculational proof starts with the keyword
``calc``, and has the following syntax:
-->

一个计算式证明是指一串使用诸如等式的传递性等基本规则得到的中间结果。在 Lean 中，计算式证明从关键字 ``calc`` 开始，语法如下：

```
calc
  <expr>_0  'op_1'  <expr>_1  ':='  <proof>_1
  '_'       'op_2'  <expr>_2  ':='  <proof>_2
  ...
  '_'       'op_n'  <expr>_n  ':='  <proof>_n
```

<!--
Note that the `calc` relations all have the same indentation. Each
``<proof>_i`` is a proof for ``<expr>_{i-1} op_i <expr>_i``.

We can also use `_` in the first relation (right after ``<expr>_0``)
which is useful to align the sequence of relation/proof pairs:
-->

`calc` 下的每一行使用相同的缩进。每个 ``<proof>_i`` 是 ``<expr>_{i-1} op_i <expr>_i`` 的证明。

我们也可以在第一个关系中使用 `_`(就在 ``<expr>_0`` 之后)，这对于对齐关系/证明对的序列很有用:

```
calc <expr>_0
    '_' 'op_1' <expr>_1 ':=' <proof>_1
    '_' 'op_2' <expr>_2 ':=' <proof>_2
    ...
    '_' 'op_n' <expr>_n ':=' <proof>_n
```

<!--
Here is an example:
-->

例子：

```lean
variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4
```

<!--
This style of writing proofs is most effective when it is used in
conjunction with the ``simp`` and ``rewrite`` tactics, which are
discussed in greater detail in the next chapter. For example, using
the abbreviation ``rw`` for rewrite, the proof above could be written
as follows:
-->

这种写证明的风格在与 `simp` 和 `rewrite` 策略（Tactic）结合使用时最为有效，这些策略将在下一章详细讨论。例如，用缩写 `rw` 表示重写，上面的证明可以写成如下。

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

<!--
Essentially, the ``rw`` tactic uses a given equality (which can be a
hypothesis, a theorem name, or a complex term) to "rewrite" the
goal. If doing so reduces the goal to an identity ``t = t``, the
tactic applies reflexivity to prove it.

Rewrites can be applied sequentially, so that the proof above can be
shortened to this:
-->

本质上，``rw`` 策略使用一个给定的等式(它可以是一个假设、一个定理名称或一个复杂的项)来「重写」目标。如果这样做将目标简化为一种等式 ``t = t``，那么该策略将使用反身性来证明这一点。

重写可以一次应用一系列，因此上面的证明可以缩写为：

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  calc
    a = d + 1  := by rw [h1, h2, h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]
```

<!--
Or even this:
-->

甚至更简单：

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]
```

<!--
The ``simp`` tactic, instead, rewrites the goal by applying the given
identities repeatedly, in any order, anywhere they are applicable in a
term. It also uses other rules that have been previously declared to
the system, and applies commutativity wisely to avoid looping. As a
result, we can also prove the theorem as follows:
-->

相反，``simp`` 策略通过在项中以任意顺序在任何适用的地方重复应用给定的等式来重写目标。它还使用了之前声明给系统的其他规则，并明智地应用交换性以避免循环。因此，我们也可以如下证明定理:

```lean
# variable (a b c d e : Nat)
# variable (h1 : a = b)
# variable (h2 : b = c + 1)
# variable (h3 : c = d)
# variable (h4 : e = 1 + d)
theorem T : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]
```

<!--
We will discuss variations of ``rw`` and ``simp`` in the next chapter.

The ``calc`` command can be configured for any relation that supports
some form of transitivity. It can even combine different relations.
-->

我们将在下一章讨论 ``rw`` 和 ``simp`` 的变体。

``calc`` 命令可以配置为任何支持某种形式的传递性的关系式。它甚至可以结合不同的关系式。

```lean
example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
```

<!--
You can "teach" `calc` new transitivity theorems by adding new instances
of the `Trans` type class. Type classes are introduced later, but the following
small example demonstrates how to extend the `calc` notation using new `Trans` instances.
-->

你可以通过添加 `Trans` 类型类（Type class）的新实例来「教给」`calc` 新的传递性定理。稍后将介绍类型类，但下面的小示例将演示如何使用新的 `Trans` 实例扩展 `calc` 表示法。

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

infix:50 " ∣ " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x ∣ y   := h₁
    _ = z   := h₂
    _ ∣ 2*z := divides_mul ..
```

<!--
The example above also makes it clear that you can use `calc` even if you
do not have an infix notation for your relation. Finally we remark that
the vertical bar `∣` in the example above is the unicode one. We use
unicode to make sure we do not overload the ASCII `|` used in the
`match .. with` expression.
-->

上面的例子也清楚地表明，即使关系式没有中缀符号，也可以使用 `calc`。最后，我们注意到上面例子中的竖线`∣`是unicode。我们使用 unicode 来确保我们不会重载在`match .. with`表达式中使用的ASCII`|`。

<!--
With ``calc``, we can write the proof in the last section in a more
natural and perspicuous way.
-->

使用 ``calc``，我们可以以一种更自然、更清晰的方式写出上一节的证明。

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]
```

<!--
The alternative `calc` notation is worth considering here. When the
first expression is taking this much space, using `_` in the first
relation naturally aligns all relations:
-->

这里值得考虑另一种 `calc` 表示法。当第一个表达式占用这么多空间时，在第一个关系中使用 `_` 自然会对齐所有关系式:

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
```

<!--
Here the left arrow before ``Nat.add_assoc`` tells rewrite to use the
identity in the opposite direction. (You can enter it with ``\l`` or
use the ascii equivalent, ``<-``.) If brevity is what we are after,
both ``rw`` and ``simp`` can do the job on their own:
-->

``Nat.add_assoc`` 之前的左箭头指挥重写以相反的方向使用等式。(你可以输入 ``\l`` 或 ascii 码 ``<-``。)如果追求简洁，``rw`` 和 ``simp`` 可以一次性完成这项工作:

```lean
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
```

<!--
The Existential Quantifier
--------------------------
-->

## 存在量词

<!--
Finally, consider the existential quantifier, which can be written as
either ``exists x : α, p x`` or ``∃ x : α, p x``.  Both versions are
actually notationally convenient abbreviations for a more long-winded
expression, ``Exists (fun x : α => p x)``, defined in Lean's library.

As you should by now expect, the library includes both an introduction
rule and an elimination rule. The introduction rule is
straightforward: to prove ``∃ x : α, p x``, it suffices to provide a
suitable term ``t`` and a proof of ``p t``. Here are some examples:
-->

存在量词可以写成 ``exists x : α, p x`` 或 ``∃ x : α, p x``。这两个写法实际上在 Lean 的库中的定义为一个更冗长的表达式，``Exists (fun x : α => p x)``。

存在量词也有一个引入规则和一个消去规则。引入规则很简单：要证明 ``∃ x : α, p x``，只需提供一个合适的项 ``t`` 和对 ``p t`` 的证明即可。``∃`` 用 ``\exists`` 或简写 ``\ex`` 输入，下面是一些例子:

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro -- ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p
```

<!--
We can use the anonymous constructor notation ``⟨t, h⟩`` for
``Exists.intro t h``, when the type is clear from the context.
-->

当类型可从上下文中推断时，我们可以使用匿名构造子表示法 ``⟨t, h⟩`` 替换 ``Exists.intro t h``。

```lean
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩
```

<!--
Note that ``Exists.intro`` has implicit arguments: Lean has to infer
the predicate ``p : α → Prop`` in the conclusion ``∃ x, p x``.  This
is not a trivial affair. For example, if we have
``hg : g 0 0 = 0`` and write ``Exists.intro 0 hg``, there are many possible values
for the predicate ``p``, corresponding to the theorems ``∃ x, g x x = x``,
``∃ x, g x x = 0``, ``∃ x, g x 0 = x``, etc. Lean uses the
context to infer which one is appropriate. This is illustrated in the
following example, in which we set the option ``pp.explicit`` to true
to ask Lean's pretty-printer to show the implicit arguments.
-->

注意 ``Exists.intro`` 有隐参数：Lean 必须在结论 ``∃ x, p x`` 中推断谓词 ``p : α → Prop``。这不是一件小事。例如，如果我们有 ``hg : g 0 0 = 0`` 和 ``Exists.intro 0 hg``，有许多可能的值的谓词 ``p``，对应定理 ``∃ x, g x x = x``，``∃ x, g x x = 0``，``∃ x, g x 0 = x``，等等。Lean 使用上下文来推断哪个是合适的。下面的例子说明了这一点，在这个例子中，我们设置了选项 ``pp.explicit`` 为true，要求 Lean 打印隐参数。

<!--
```lean
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4
```
-->

```lean
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- 打印隐参数
#print gex1
#print gex2
#print gex3
#print gex4
```

<!--
We can view ``Exists.intro`` as an information-hiding operation, since
it hides the witness to the body of the assertion. The existential
elimination rule, ``Exists.elim``, performs the opposite operation. It
allows us to prove a proposition ``q`` from ``∃ x : α, p x``, by
showing that ``q`` follows from ``p w`` for an arbitrary value
``w``. Roughly speaking, since we know there is an ``x`` satisfying
``p x``, we can give it a name, say, ``w``. If ``q`` does not mention
``w``, then showing that ``q`` follows from ``p w`` is tantamount to
showing that ``q`` follows from the existence of any such ``x``. Here
is an example:
-->

我们可以将 ``Exists.intro`` 视为信息隐藏操作，因为它将断言的具体实例隐藏起来变成了存在量词。存在消去规则 ``Exists.elim`` 执行相反的操作。它允许我们从 ``∃ x : α, p x`` 证明一个命题 ``q``，通过证明对于任意值 ``w`` 时 ``p w`` 都能推出 ``q``。粗略地说，既然我们知道有一个 ``x`` 满足 ``p x``，我们可以给它起个名字，比如 ``w``。如果 ``q`` 没有提到 ``w``，那么表明 ``p w`` 能推出 ``q`` 就等同于表明 ``q`` 从任何这样的 ``x`` 的存在而推得。下面是一个例子:

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
```

<!--
It may be helpful to compare the exists-elimination rule to the
or-elimination rule: the assertion ``∃ x : α, p x`` can be thought of
as a big disjunction of the propositions ``p a``, as ``a`` ranges over
all the elements of ``α``. Note that the anonymous constructor
notation ``⟨w, hw.right, hw.left⟩`` abbreviates a nested constructor
application; we could equally well have written ``⟨w, ⟨hw.right, hw.left⟩⟩``.

Notice that an existential proposition is very similar to a sigma
type, as described in dependent types section.  The difference is that
given ``a : α`` and ``h : p a``, the term ``Exists.intro a h`` has
type ``(∃ x : α, p x) : Prop`` and ``Sigma.mk a h`` has type
``(Σ x : α, p x) : Type``. The similarity between ``∃`` and ``Σ`` is another
instance of the Curry-Howard isomorphism.

Lean provides a more convenient way to eliminate from an existential
quantifier with the ``match`` expression:
-->

把存在消去规则和析取消去规则作个比较可能会带来一些启发。命题 ``∃ x : α, p x`` 可以看成一个对所有 ``α`` 中的元素 ``a`` 所组成的命题 ``p a`` 的大型析取。注意到匿名构造子 ``⟨w, hw.right, hw.left⟩`` 是嵌套的构造子 ``⟨w, ⟨hw.right, hw.left⟩⟩`` 的缩写。

存在式命题类型很像依值类型一节所述的 sigma 类型。给定 ``a : α`` 和 ``h : p a`` 时，项 ``Exists.intro a h`` 具有类型 ``(∃ x : α, p x) : Prop``，而 ``Sigma.mk a h`` 具有类型 ``(Σ x : α, p x) : Type``。``∃`` 和 ``Σ`` 之间的相似性是Curry-Howard同构的另一例子。

Lean 提供一个更加方便的消去存在量词的途径，那就是通过 ``match`` 表达式。

```lean
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
```

<!--
The ``match`` expression is part of Lean's function definition system,
which provides convenient and expressive ways of defining complex
functions.  Once again, it is the Curry-Howard isomorphism that allows
us to co-opt this mechanism for writing proofs as well.  The ``match``
statement "destructs" the existential assertion into the components
``w`` and ``hw``, which can then be used in the body of the statement
to prove the proposition. We can annotate the types used in the match
for greater clarity:
-->

``match`` 表达式是 Lean 功能定义系统的一部分，它提供了复杂功能的方便且丰富的表达方式。再一次，正是Curry-Howard同构让我们能够采用这种机制来编写证明。``match`` 语句将存在断言「析构」到组件 ``w`` 和 ``hw`` 中，然后可以在语句体中使用它们来证明命题。我们可以对 match 中使用的类型进行注释，以提高清晰度：

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
```

<!--
We can even use the match statement to decompose the conjunction at the same time:
-->

我们甚至可以同时使用 match 语句来分解合取：

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

<!--
Lean also provides a pattern-matching ``let`` expression:
-->

Lean 还提供了一个模式匹配的 ``let`` 表达式：

```lean
# variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
```

<!--
This is essentially just alternative notation for the ``match``
construct above. Lean will even allow us to use an implicit ``match``
in the ``fun`` expression:
-->

这实际上是上面的 ``match`` 结构的替代表示法。Lean 甚至允许我们在 ``fun`` 表达式中使用隐含的 ``match``：


```lean
# variable (α : Type) (p q : α → Prop)
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
```

<!--
We will see in [Chapter Induction and Recursion](./induction_and_recursion.md) that all these variations are
instances of a more general pattern-matching construct.

In the following example, we define ``is_even a`` as ``∃ b, a = 2 * b``,
and then we show that the sum of two even numbers is an even number.
-->

我们将在[归纳和递归](./induction_and_recursion.md)一章看到所有这些变体都是更一般的模式匹配构造的实例。

在下面的例子中，我们将 ``even a`` 定义为 ``∃ b, a = 2 * b``，然后我们证明两个偶数的和是偶数。


```lean
def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))
```

<!--
Using the various gadgets described in this chapter --- the match
statement, anonymous constructors, and the ``rewrite`` tactic, we can
write this proof concisely as follows:
-->

使用本章描述的各种小工具——``match`` 语句、匿名构造子和 ``rewrite`` 策略，我们可以简洁地写出如下证明：

```lean
# def is_even (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
```

<!--
Just as the constructive "or" is stronger than the classical "or," so,
too, is the constructive "exists" stronger than the classical
"exists". For example, the following implication requires classical
reasoning because, from a constructive standpoint, knowing that it is
not the case that every ``x`` satisfies ``¬ p`` is not the same as
having a particular ``x`` that satisfies ``p``.
-->

就像构造主义的「或」比古典的「或」强，同样，构造的「存在」也比古典的「存在」强。例如，下面的推论需要经典推理，因为从构造的角度来看，知道并不是每一个 ``x`` 都满足 ``¬ p``，并不等于有一个特定的 ``x`` 满足 ``p``。

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

<!--
What follows are some common identities involving the existential
quantifier. In the exercises below, we encourage you to prove as many
as you can. We also leave it to you to determine which are
nonconstructive, and hence require some form of classical reasoning.
-->

下面是一些涉及存在量词的常见等式。在下面的练习中，我们鼓励你尽可能多写出证明。你需要判断哪些是非构造主义的，因此需要一些经典推理。

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

<!--
Notice that the second example and the last two examples require the
assumption that there is at least one element ``a`` of type ``α``.

Here are solutions to two of the more difficult ones:
-->

注意，第二个例子和最后两个例子要求假设至少有一个类型为 ``α`` 的元素 ``a``。

以下是两个比较困难的问题的解：

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

<!--
More on the Proof Language
--------------------------
-->

## 多来点儿证明语法

<!--
We have seen that keywords like ``fun``, ``have``, and ``show`` make
it possible to write formal proof terms that mirror the structure of
informal mathematical proofs. In this section, we discuss some
additional features of the proof language that are often convenient.

To start with, we can use anonymous "have" expressions to introduce an
auxiliary goal without having to label it. We can refer to the last
expression introduced in this way using the keyword ``this``:
-->

我们已经看到像 ``fun``、``have`` 和 ``show`` 这样的关键字使得写出反映非正式数学证明结构的正式证明项成为可能。在本节中，我们将讨论证明语言的一些通常很方便的附加特性。

首先，我们可以使用匿名的 ``have`` 表达式来引入一个辅助目标，而不需要标注它。我们可以使用关键字 ``this`` 来引用最后一个以这种方式引入的表达式:

```lean
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
```

<!--
Often proofs move from one fact to the next, so this can be effective
in eliminating the clutter of lots of labels.

When the goal can be inferred, we can also ask Lean instead to fill in
the proof by writing ``by assumption``:
-->

通常证明从一个事实转移到另一个事实，所以这可以有效地消除杂乱的大量标签。

当目标可以推断出来时，我们也可以让 Lean 写 ``by assumption`` 来填写证明：

```lean
# variable (f : Nat → Nat)
# variable (h : ∀ x : Nat, f x ≤ f (x + 1))
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
```

<!--
This tells Lean to use the ``assumption`` tactic, which, in turn,
proves the goal by finding a suitable hypothesis in the local
context. We will learn more about the ``assumption`` tactic in the
next chapter.

We can also ask Lean to fill in the proof by writing ``‹p›``, where
``p`` is the proposition whose proof we want Lean to find in the
context.  You can type these corner quotes using ``\f<`` and ``\f>``,
respectively. The letter "f" is for "French," since the unicode
symbols can also be used as French quotation marks. In fact, the
notation is defined in Lean as follows:
-->

这告诉 Lean 使用 ``assumption`` 策略，反过来，通过在局部上下文中找到合适的假设来证明目标。我们将在下一章学习更多关于 ``assumption`` 策略的内容。

我们也可以通过写 ``‹p›`` 的形式要求 Lean 填写证明，其中 ``p`` 是我们希望 Lean 在上下文中找到的证明命题。你可以分别使用 ``\f<`` 和 ``\f>`` 输入这些角引号。字母「f」表示「French」，因为 unicode 符号也可以用作法语引号。事实上，这个符号在 Lean 中定义如下:

```lean
notation "‹" p "›" => show p by assumption
```

<!--
This approach is more robust than using ``by assumption``, because the
type of the assumption that needs to be inferred is given
explicitly. It also makes proofs more readable. Here is a more
elaborate example:
-->

这种方法比使用 ``by assumption`` 更稳健，因为需要推断的假设类型是显式给出的。它还使证明更具可读性。这里有一个更详细的例子:

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

<!--
Keep in mind that you can use the French quotation marks in this way
to refer to *anything* in the context, not just things that were
introduced anonymously. Its use is also not limited to propositions,
though using it for data is somewhat odd:
-->

你可以这样使用法语引号来指代上下文中的「任何东西」，而不仅仅是匿名引入的东西。它的使用也不局限于命题，尽管将它用于数据有点奇怪：

```lean
example (n : Nat) : Nat := ‹Nat›
```

<!--
Later, we show how you can extend the proof language using the Lean macro system.
-->

稍后，我们将展示如何使用 Lean 中的宏系统扩展证明语言。

<!--
Exercises
---------
-->

练习
---------

<!--
1. Prove these equivalences:
-->

1. 证明以下等式：

```lean
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
```

<!--
You should also try to understand why the reverse implication is not derivable in the last example.
-->

你还应该想想为什么在最后一个例子中反过来是不能证明的。

<!--
2. It is often possible to bring a component of a formula outside a
   universal quantifier, when it does not depend on the quantified
   variable. Try proving these (one direction of the second of these
   requires classical logic):
-->

2. 当一个公式的组成部分不依赖于被全称的变量时，通常可以把它提取出一个全称量词的范围。尝试证明这些(第二个命题中的一个方向需要经典逻辑)：

```lean
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
```

<!--
3. Consider the "barber paradox," that is, the claim that in a certain
   town there is a (male) barber that shaves all and only the men who
   do not shave themselves. Prove that this is a contradiction:
-->

3. 考虑「理发师悖论」：在一个小镇里，这里有一个（男性）理发师给所有不为自己刮胡子的人刮胡子。证明这里存在矛盾：

```lean
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
```

<!--
4. Remember that, without any parameters, an expression of type
   ``Prop`` is just an assertion. Fill in the definitions of ``prime``
   and ``Fermat_prime`` below, and construct each of the given
   assertions. For example, you can say that there are infinitely many
   primes by asserting that for every natural number ``n``, there is a
   prime number greater than ``n``. Goldbach's weak conjecture states
   that every odd number greater than 5 is the sum of three
   primes. Look up the definition of a Fermat prime or any of the
   other statements, if necessary.
-->

4. 如果没有任何参数，类型 ``Prop`` 的表达式只是一个断言。填入下面 ``prime`` 和 ``Fermat_prime`` 的定义，并构造每个给定的断言。例如，通过断言每个自然数 ``n`` 都有一个大于 ``n`` 的质数，你可以说有无限多个质数。哥德巴赫弱猜想指出，每一个大于5的奇数都是三个素数的和。如果有必要，请查阅费马素数的定义或其他任何资料。

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

<!--
5. Prove as many of the identities listed in the Existential
   Quantifier section as you can.
-->

5. 尽可能多地证明存在量词一节列出的等式。
