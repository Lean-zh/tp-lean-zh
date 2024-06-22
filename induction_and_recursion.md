<!--
Induction and Recursion
=======================
-->

归纳和递归
=======================

<!--
In the previous chapter, we saw that inductive definitions provide a
powerful means of introducing new types in Lean. Moreover, the
constructors and the recursors provide the only means of defining
functions on these types. By the propositions-as-types correspondence,
this means that induction is the fundamental method of proof.

Lean provides natural ways of defining recursive functions, performing
pattern matching, and writing inductive proofs. It allows you to
define a function by specifying equations that it should satisfy, and
it allows you to prove a theorem by specifying how to handle various
cases that can arise. Behind the scenes, these descriptions are
"compiled" down to primitive recursors, using a procedure that we
refer to as the "equation compiler." The equation compiler is not part
of the trusted code base; its output consists of terms that are
checked independently by the kernel.
-->

在上一章中，我们看到归纳定义提供了在 Lean 中引入新类型的强大手段。此外，构造子和递归器提供了在这些类型上定义函数的唯一手段。命题即类型的对应关系，意味着归纳法是证明的基本方法。

Lean 提供了定义递归函数、执行模式匹配和编写归纳证明的自然方法。它允许你通过指定它应该满足的方程来定义一个函数，它允许你通过指定如何处理可能出现的各种情况来证明一个定理。在它内部，这些描述被「方程编译器」程序「编译」成原始递归器。方程编译器不是可信代码库的一部分；它的输出包括由内核独立检查的项。

<!--
Pattern Matching
----------------
-->

模式匹配
----------------

<!--
The interpretation of schematic patterns is the first step of the
compilation process. We have seen that the ``casesOn`` recursor can
be used to define functions and prove theorems by cases, according to
the constructors involved in an inductively defined type. But
complicated definitions may use several nested ``casesOn``
applications, and may be hard to read and understand. Pattern matching
provides an approach that is more convenient, and familiar to users of
functional programming languages.

Consider the inductively defined type of natural numbers. Every
natural number is either ``zero`` or ``succ x``, and so you can define
a function from the natural numbers to an arbitrary type by specifying
a value in each of those cases:
-->

对示意图模式的解释是编译过程的第一步。我们已经看到，`casesOn` 递归器可以通过分情况讨论来定义函数和证明定理，根据归纳定义类型所涉及的构造子。但是复杂的定义可能会使用几个嵌套的 ``casesOn`` 应用，而且可能很难阅读和理解。模式匹配提供了一种更方便的方法，并且为函数式编程语言的用户所熟悉。

考虑一下自然数的归纳定义类型。每个自然数要么是 ``zero``，要么是 ``succ x``，因此你可以通过在每个情况下指定一个值来定义一个从自然数到任意类型的函数：

```lean
open Nat

def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x

def isZero : Nat → Bool
  | zero   => true
  | succ x => false
```

<!--
The equations used to define these functions hold definitionally:
-->

用来定义这些函数的方程在定义上是成立的：

```lean
# open Nat
# def sub1 : Nat → Nat
#   | zero   => zero
#   | succ x => x
# def isZero : Nat → Bool
#   | zero   => true
#   | succ x => false
example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl
```

<!--
Instead of ``zero`` and ``succ``, we can use more familiar notation:
-->

我们可以用一些更耳熟能详的符号，而不是 ``zero`` 和 ``succ``：

```lean
def sub1 : Nat → Nat
  | 0   => 0
  | x+1 => x

def isZero : Nat → Bool
  | 0   => true
  | x+1 => false
```

<!--
Because addition and the zero notation have been assigned the
``[match_pattern]`` attribute, they can be used in pattern matching. Lean
simply normalizes these expressions until the constructors ``zero``
and ``succ`` are exposed.

Pattern matching works with any inductive type, such as products and option types:
-->

因为加法和零符号已经被赋予 `[matchPattern]` 属性，它们可以被用于模式匹配。Lean 简单地将这些表达式规范化，直到显示构造子 ``zero`` 和 ``succ``。

模式匹配适用于任何归纳类型，如乘积和 Option 类型：

```lean
def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none   => 0
```

<!--
Here we use it not only to define a function, but also to carry out a
proof by cases:
-->

在这里，我们不仅用它来定义一个函数，而且还用它来进行逐情况证明：

```lean
# namespace Hidden
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => rfl  -- proof that not (not true) = true
  | false => rfl  -- proof that not (not false) = false
# end Hidden
```

<!--
Pattern matching can also be used to destruct inductively defined propositions:
-->

模式匹配也可以用来解构归纳定义的命题：

```lean
example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

<!--
This provides a compact way of unpacking hypotheses that make use of logical connectives.

In all these examples, pattern matching was used to carry out a single
case distinction. More interestingly, patterns can involve nested
constructors, as in the following examples.
-->

这样解决带逻辑连接词的命题就很紧凑。

在所有这些例子中，模式匹配被用来进行单一情况的区分。更有趣的是，模式可以涉及嵌套的构造子，如下面的例子。

```lean
def sub2 : Nat → Nat
  | 0   => 0
  | 1   => 0
  | x+2 => x
```

<!--
The equation compiler first splits on cases as to whether the input is
``zero`` or of the form ``succ x``.  It then does a case split on
whether ``x`` is of the form ``zero`` or ``succ x``.  It determines
the necessary case splits from the patterns that are presented to it,
and raises an error if the patterns fail to exhaust the cases. Once
again, we can use arithmetic notation, as in the version below. In
either case, the defining equations hold definitionally.
-->

方程编译器首先对输入是 ``zero`` 还是 ``succ x`` 的形式进行分类讨论，然后对 `x` 是 ``zero`` 还是 ``succ x`` 的形式进行分类讨论。它从提交给它的模式中确定必要的情况拆分，如果模式不能穷尽情况，则会引发错误。同时，我们可以使用算术符号，如下面的版本。在任何一种情况下，定义方程都是成立的。

```lean
# def sub2 : Nat → Nat
#   | 0   => 0
#   | 1   => 0
#   | x+2 => x
example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl

example : sub2 5 = 3 := rfl
```

<!--
You can write ``#print sub2`` to see how the function was compiled to
recursors. (Lean will tell you that ``sub2`` has been defined in terms
of an internal auxiliary function, ``sub2.match_1``, but you can print
that out too.) Lean uses these auxiliary functions to compile `match` expressions.
Actually, the definition above is expanded to
-->

你可以写 ``#print sub2`` 来看看这个函数是如何被编译成递归器的。（Lean 会告诉你 `sub2` 已经被定义为内部辅助函数 `sub2.match_1`，但你也可以把它打印出来）。Lean 使用这些辅助函数来编译 `match` 表达式。实际上，上面的定义被扩展为

```lean
def sub2 : Nat → Nat :=
  fun x =>
    match x with
    | 0   => 0
    | 1   => 0
    | x+2 => x
```

<!--
Here are some more examples of nested pattern matching:
-->

下面是一些嵌套模式匹配的例子：

```lean
example (p q : α → Prop)
        : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def foo : Nat × Nat → Nat
  | (0, n)     => 0
  | (m+1, 0)   => 1
  | (m+1, n+1) => 2
```

<!--
The equation compiler can process multiple arguments sequentially. For
example, it would be more natural to define the previous example as a
function of two arguments:
-->

方程编译器可以按顺序处理多个参数。例如，将前面的例子定义为两个参数的函数会更自然：

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

<!--
Here is another example:
-->

另一例：

```lean
def bar : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b
```

<!--
Note that the patterns are separated by commas.

In each of the following examples, splitting occurs on only the first
argument, even though the others are included among the list of
patterns.
-->

这些模式是由逗号分隔的。

在下面的每个例子中，尽管其他参数包括在模式列表中，但只对第一个参数进行了分割。

```lean
# namespace Hidden
def and : Bool → Bool → Bool
  | true,  a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | true,  _ => true
  | false, a => a

def cond : Bool → α → α → α
  | true,  x, y => x
  | false, x, y => y
# end Hidden
```

<!--
Notice also that, when the value of an argument is not needed in the
definition, you can use an underscore instead. This underscore is
known as a *wildcard pattern*, or an *anonymous variable*. In contrast
to usage outside the equation compiler, here the underscore does *not*
indicate an implicit argument. The use of underscores for wildcards is
common in functional programming languages, and so Lean adopts that
notation. [Section Wildcards and Overlapping Patterns](#wildcards-and-overlapping-patterns)
expands on the notion of a wildcard, and [Section Inaccessible Patterns](#inaccessible-patterns) explains how
you can use implicit arguments in patterns as well.

As described in [Chapter Inductive Types](./inductive_types.md),
inductive data types can depend on parameters. The following example defines
the ``tail`` function using pattern matching. The argument ``α : Type u``
is a parameter and occurs before the colon to indicate it does not participate in the pattern matching.
Lean also allows parameters to occur after ``:``, but it cannot pattern match on them.
-->

还要注意的是，当定义中不需要一个参数的值时，你可以用下划线来代替。这个下划线被称为 **通配符模式** ，或 **匿名变量** 。与方程编译器之外的用法不同，这里的下划线 **并不** 表示一个隐参数。使用下划线表示通配符在函数式编程语言中是很常见的，所以 Lean 采用了这种符号。[通配符和重叠模式](#通配符和重叠模式)一节阐述了通配符的概念，而[不可访问模式](#不可访问模式)一节解释了你如何在模式中使用隐参数。

正如[归纳类型](./inductive_types.md)一章中所描述的，归纳数据类型可以依赖于参数。下面的例子使用模式匹配定义了 ``tail`` 函数。参数 ``α : Type`` 是一个参数，出现在冒号之前，表示它不参与模式匹配。Lean 也允许参数出现在 ``:`` 之后，但它不能对其进行模式匹配。

```lean
def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as
```

<!--
Despite the different placement of the parameter ``α`` in these two
examples, in both cases it is treated in the same way, in that it does
not participate in a case split.

Lean can also handle more complex forms of pattern matching, in which
arguments to dependent types pose additional constraints on the
various cases. Such examples of *dependent pattern matching* are
considered in the [Section Dependent Pattern Matching](#dependent-pattern-matching).

-->

尽管参数 ``α`` 在这两个例子中的位置不同，但在这两种情况下，它的处理方式是一样的，即它不参与情况分割。

Lean 也可以处理更复杂的模式匹配形式，其中从属类型的参数对各种情况构成了额外的约束。这种 **依值模式匹配** 的例子在[依值模式匹配](#依值模式匹配)一节中考虑。

<!--
Wildcards and Overlapping Patterns
----------------------------------
-->

通配符和重叠模式
----------------------------------

<!--
Consider one of the examples from the last section:
-->

考虑上节的一个例子：

```lean
def foo : Nat → Nat → Nat
  | 0,   n   => 0
  | m+1, 0   => 1
  | m+1, n+1 => 2
```

<!--
An alternative presentation is:
-->

也可以表述成

```lean
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
```

<!--
In the second presentation, the patterns overlap; for example, the
pair of arguments ``0 0`` matches all three cases. But Lean handles
the ambiguity by using the first applicable equation, so in this example
the net result is the same. In particular, the following equations hold
definitionally:
-->

在第二种表述中，模式是重叠的；例如，一对参数 ``0 0`` 符合所有三种情况。但是Lean 通过使用第一个适用的方程来处理这种模糊性，所以在这个例子中，最终结果是一样的。特别是，以下方程在定义上是成立的：

```lean
# def foo : Nat → Nat → Nat
#   | 0, n => 0
#   | m, 0 => 1
#   | m, n => 2
example : foo 0     0     = 0 := rfl
example : foo 0     (n+1) = 0 := rfl
example : foo (m+1) 0     = 1 := rfl
example : foo (m+1) (n+1) = 2 := rfl
```

<!--
Since the values of ``m`` and ``n`` are not needed, we can just as well use wildcard patterns instead.
-->

由于不需要 ``m`` 和 ``n`` 的值，我们也可以用通配符模式代替。

```lean
def foo : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2
```

<!--
You can check that this definition of ``foo`` satisfies the same
definitional identities as before.

Some functional programming languages support *incomplete
patterns*. In these languages, the interpreter produces an exception
or returns an arbitrary value for incomplete cases. We can simulate
the arbitrary value approach using the ``Inhabited`` type
class. Roughly, an element of ``Inhabited α`` is a witness to the fact
that there is an element of ``α``; in the [Chapter Type Classes](./type_classes.md)
we will see that Lean can be instructed that suitable
base types are inhabited, and can automatically infer that other
constructed types are inhabited. On this basis, the
standard library provides a default element, ``default``, of
any inhabited type.

We can also use the type ``Option α`` to simulate incomplete patterns.
The idea is to return ``some a`` for the provided patterns, and use
``none`` for the incomplete cases. The following example demonstrates
both approaches.
-->

你可以检查这个 ``foo`` 的定义是否满足与之前相同的定义特性。

一些函数式编程语言支持 **不完整的模式** 。在这些语言中，解释器对不完整的情况产生一个异常或返回一个任意的值。我们可以使用 ``Inhabited`` （含元素的）类型类来模拟任意值的方法。粗略的说，``Inhabited α`` 的一个元素是对 ``α`` 拥有一个元素的见证；在[类型类](./type_classes.md)中，我们将看到 Lean 可以被告知合适的基础类型是含元素的，并且可以自动推断出其他构造类型是含元素的。在此基础上，标准库提供了一个任意元素 ``arbitrary``，任何含元素的类型。

我们还可以使用类型`Option α`来模拟不完整的模式。我们的想法是对所提供的模式返回`some a`，而对不完整的情况使用`none`。下面的例子演示了这两种方法。

<!--
```lean
def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- the "incomplete" case

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl
```
-->

```lean
def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- 不完整的模式

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- 不完整的模式

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl
```

<!--
The equation compiler is clever. If you leave out any of the cases in
the following definition, the error message will let you know what has
not been covered.
-->

方程编译器是很智能的。如果你遗漏了以下定义中的任何一种情况，错误信息会告诉你遗漏了哪个。

```lean
def bar : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b
```

<!--
It will also use an "if ... then ... else" instead of a ``casesOn`` in appropriate situations.
-->

某些情况也可以用「if ... then ... else」代替 ``casesOn``。

```lean
def foo : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
```

<!--
Structural Recursion and Induction
----------------------------------
-->

结构化递归和归纳
----------------------------------

<!--
What makes the equation compiler powerful is that it also supports
recursive definitions. In the next three sections, we will describe,
respectively:

- structurally recursive definitions
- well-founded recursive definitions
- mutually recursive definitions

Generally speaking, the equation compiler processes input of the following form:

-->

方程编译器的强大之处在于，它还支持递归定义。在接下来的三节中，我们将分别介绍。

- 结构性递归定义
- 良基的递归定义
- 相互递归的定义

一般来说，方程编译器处理以下形式的输入。

```
def foo (a : α) : (b : β) → γ
  | [patterns₁] => t₁
  ...
  | [patternsₙ] => tₙ
```

<!--
Here ``(a : α)`` is a sequence of parameters, ``(b : β)`` is the
sequence of arguments on which pattern matching takes place, and ``γ``
is any type, which can depend on ``a`` and ``b``. Each line should
contain the same number of patterns, one for each element of ``β``. As we
have seen, a pattern is either a variable, a constructor applied to
other patterns, or an expression that normalizes to something of that
form (where the non-constructors are marked with the ``[match_pattern]``
attribute). The appearances of constructors prompt case splits, with
the arguments to the constructors represented by the given
variables. In [Section Dependent Pattern Matching](#dependent-pattern-matching),
we will see that it is sometimes necessary to include explicit terms in patterns that
are needed to make an expression type check, though they do not play a
role in pattern matching. These are called "inaccessible patterns" for
that reason. But we will not need to use such inaccessible patterns
before [Section Dependent Pattern Matching](#dependent-pattern-matching).

As we saw in the last section, the terms ``t₁, ..., tₙ`` can make use
of any of the parameters ``a``, as well as any of the variables that
are introduced in the corresponding patterns. What makes recursion and
induction possible is that they can also involve recursive calls to
``foo``. In this section, we will deal with *structural recursion*, in
which the arguments to ``foo`` occurring on the right-hand side of the
``=>`` are subterms of the patterns on the left-hand side. The idea is
that they are structurally smaller, and hence appear in the inductive
type at an earlier stage. Here are some examples of structural
recursion from the last chapter, now defined using the equation
compiler:
-->

这里 `(a : α)` 是一个参数序列，`(b : β)` 是进行模式匹配的参数序列，`γ` 是任何类型，它可以取决于 `a` 和 `b `。每一行应该包含相同数量的模式，对应于 `β` 的每个元素。正如我们所看到的，模式要么是一个变量，要么是应用于其他模式的构造子，要么是一个正规化为该形式的表达式（其中非构造子用 ``[matchPattern]`` 属性标记）。构造子的出现会提示情况拆分，构造子的参数由给定的变量表示。在[依值模式匹配](#依值模式匹配)一节中，我们将看到有时有必要在模式中包含明确的项，这些项需要进行表达式类型检查，尽管它们在模式匹配中没有起到作用。由于这个原因，这些被称为「不可访问的模式」。但是在[依值模式匹配](#依值模式匹配)一节之前，我们将不需要使用这种不可访问的模式。

正如我们在上一节所看到的，项 `t₁,...,tₙ` 可以利用任何一个参数 `a`，以及在相应模式中引入的任何一个变量。使得递归和归纳成为可能的是，它们也可以涉及对 ``foo`` 的递归调用。在本节中，我们将处理 **结构性递归** ，其中 `foo` 的参数出现在 `:=` 的右侧，是左侧模式的子项。我们的想法是，它们在结构上更小，因此在归纳类型中出现在更早的阶段。下面是上一章的一些结构递归的例子，现在用方程编译器来定义。

```lean
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat)   : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

def mul : Nat → Nat → Nat
  | n, zero   => zero
  | n, succ m => add (mul n m) n
```
<!--

The proof of ``zero_add`` makes it clear that proof by induction is
really a form of recursion in Lean.

The example above shows that the defining equations for ``add`` hold
definitionally, and the same is true of ``mul``. The equation compiler
tries to ensure that this holds whenever possible, as is the case with
straightforward structural induction. In other situations, however,
reductions hold only *propositionally*, which is to say, they are
equational theorems that must be applied explicitly. The equation
compiler generates such theorems internally. They are not meant to be
used directly by the user; rather, the `simp` tactic
is configured to use them when necessary. Thus both of the following
proofs of `zero_add` work:
-->

``zero_add`` 的证明清楚地表明，归纳证明实际上是 Lean 中的一种递归形式。

上面的例子表明，``add`` 的定义方程具有定义意义，`` mul`` 也是如此。方程编译器试图确保在任何可能的情况下都是这样，就像直接的结构归纳法一样。然而，在其他情况下，约简只在命题上成立，也就是说，它们是必须明确应用的方程定理。方程编译器在内部生成这样的定理。用户不能直接使用它们;相反，``simp`` 策略被配置为在必要时使用它们。因此，对`zero_add`的以下两种证明都成立：

```lean
open Nat
# def add : Nat → Nat → Nat
#   | m, zero   => m
#   | m, succ n => succ (add m n)
theorem zero_add : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]
```

<!--
As with definition by pattern matching, parameters to a structural
recursion or induction may appear before the colon. Such parameters
are simply added to the local context before the definition is
processed. For example, the definition of addition may also be written
as follows:
-->

与模式匹配定义一样，结构递归或归纳的参数可能出现在冒号之前。在处理定义之前，简单地将这些参数添加到本地上下文中。例如，加法的定义也可以写成这样:

```lean
open Nat
def add (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)
```

<!--
You can also write the example above using `match`.
-->

你也可以用 ``match`` 来写上面的例子。

```lean
open Nat
def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)
```

<!--
A more interesting example of structural recursion is given by the Fibonacci function ``fib``.
-->

一个更有趣的结构递归的例子是斐波那契函数 ``fib``。

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl
```

<!--
Here, the value of the ``fib`` function at ``n + 2`` (which is
definitionally equal to ``succ (succ n)``) is defined in terms of the
values at ``n + 1`` (which is definitionally equivalent to ``succ n``)
and the value at ``n``. This is a notoriously inefficient way of
computing the Fibonacci function, however, with an execution time that
is exponential in ``n``. Here is a better way:
-->

这里，``fib`` 函数在 ``n + 2`` （定义上等于 ``succ (succ n)`` ）处的值是根据 ``n + 1`` （定义上等价于 ``succ n`` ）和 ``n`` 处的值定义的。然而，这是一种众所周知的计算斐波那契函数的低效方法，其执行时间是 ``n`` 的指数级。这里有一个更好的方法:

```lean
def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100
```

<!--
Here is the same definition using a `let rec` instead of a `where`.
-->

下面是相同的定义，使用 ``let rec`` 代替 ``where``。


```lean
def fibFast (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2
```

<!--
In both cases, Lean generates the auxiliary function `fibFast.loop`.

To handle structural recursion, the equation compiler uses
*course-of-values* recursion, using constants ``below`` and ``brecOn``
that are automatically generated with each inductively defined
type. You can get a sense of how it works by looking at the types of
``Nat.below`` and ``Nat.brecOn``:
-->

在这两种情况下，Lean 都会生成辅助函数 ``fibFast.loop``。

为了处理结构递归，方程编译器使用 **值过程** （course-of-values）递归，使用由每个归纳定义类型自动生成的常量 `below` 和 `brecOn`。你可以通过查看 ``Nat.below`` 和 ``Nat.brecOn`` 的类型来了解它是如何工作的。

```lean
variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
```

<!--
The type ``@Nat.below C (3 : nat)`` is a data structure that stores elements of ``C 0``, ``C 1``, and ``C 2``.
The course-of-values recursion is implemented by ``Nat.brecOn``. It enables us to define the value of a dependent
function of type ``(n : Nat) → C n`` at a particular input ``n`` in terms of all the previous values of the function,
presented as an element of ``@Nat.below C n``.

The use of course-of-values recursion is one of the techniques the equation compiler uses to justify to
the Lean kernel that a function terminates. It does not affect the code generator which compiles recursive
functions as other functional programming language compilers. Recall that `#eval fib <n>` is exponential on `<n>`.
On the other hand, `#reduce fib <n>` is efficient because it uses the definition sent to the kernel that
is based on the `brecOn` construction.
-->

类型 ``@Nat.below C (3 : nat)`` 是一个存储着 ``C 0``，``C 1``，和 ``C 2`` 中元素的数据结构。值过程递归由 ``Nat.brecOn`` 实现。它根据该函数之前的所有值，定义类型为 ``(n : Nat) → C n`` 的依值函数在特定输入 ``n`` 时的值，表示为 ``@Nat.below C n`` 的一个元素。

值过程递归是方程编译器用来向 Lean 内核证明函数终止的技术之一。它不会像其他函数式编程语言编译器一样影响编译递归函数的代码生成器。回想一下，`#eval fib <n>` 是 `<n>` 的指数。另一方面，`#reduce fib <n>` 是有效的，因为它使用了发送到内核的基于 `brecOn` 结构的定义。

<!--
```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- #eval fib 50 -- slow
#reduce fib 50  -- fast

#print fib
```
-->

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- #eval fib 50 -- 这个很慢
#reduce fib 50  -- 用这个，这个快

#print fib
```

<!--
Another good example of a recursive definition is the list ``append`` function.
-->

另一个递归定义的好例子是列表的 ``append`` 函数。

```lean
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
```

<!--
Here is another: it adds elements of the first list to elements of the second list, until one of the two lists runs out.
-->

这里是另一个：它将第一个列表中的元素和第二个列表中的元素分别相加，直到两个列表中的一个用尽。

```lean
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10]
-- [5, 7, 9]
```

<!--
You are encouraged to experiment with similar examples in the exercises below.
-->

你可以在章末练习中尝试类似的例子。

<!--
Local recursive declarations
---------
-->

局域递归声明
---------

<!--
You can define local recursive declarations using the `let rec` keyword.
-->

可以使用 ``let rec`` 关键字定义局域递归声明。

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α
```

<!--
Lean creates an auxiliary declaration for each `let rec`. In the example above,
it created the declaration `replicate.loop` for the `let rec loop` occurring at `replicate`.
Note that, Lean "closes" the declaration by adding any local variable occurring in the
`let rec` declaration as additional parameters. For example, the local variable `a` occurs
at `let rec loop`.

You can also use `let rec` in tactic mode and for creating proofs by induction.
-->

Lean 为每个 ``let rec`` 创建一个辅助声明。在上面的例子中，它对于出现在 ``replicate`` 的 ``let rec loop`` 创建了声明 ``replication.loop``。请注意，Lean 通过添加 ``let rec`` 声明中出现的任何局部变量作为附加参数来「关闭」声明。例如，局部变量 ``a`` 出现在 ``let rec`` 循环中。

你也可以在策略证明模式中使用 ``let rec``，并通过归纳来创建证明。

```lean
# def replicate (n : Nat) (a : α) : List α :=
#  let rec loop : Nat → List α → List α
#    | 0,   as => as
#    | n+1, as => loop n (a::as)
#  loop n []
theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
  exact aux n []
```

<!--
You can also introduce auxiliary recursive declarations using `where` clause after your definition.
Lean converts them into a `let rec`.
-->

还可以在定义后使用 ``where`` 子句引入辅助递归声明。Lean 将它们转换为 ``let rec``。

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
```

<!--
Well-Founded Recursion and Induction
------------------------------------
-->

良基递归和归纳
------------------------------------

<!--
When structural recursion cannot be used, we can prove termination using well-founded recursion.
We need a well-founded relation and a proof that each recursive application is decreasing with respect to
this relation. Dependent type theory is powerful enough to encode and justify
well-founded recursion. Let us start with the logical background that
is needed to understand how it works.

Lean's standard library defines two predicates, ``Acc r a`` and
``WellFounded r``, where ``r`` is a binary relation on a type ``α``,
and ``a`` is an element of type ``α``.
-->

当不能使用结构递归时，我们可以使用良基递归（well-founded recursion）来证明终止性。我们需要一个良基关系和一个证明每个递归调用相对于该关系都是递减的证明。依值类型理论具有足够的表达能力来编码和证明良基递归。让我们从理解其工作原理所需的逻辑背景开始。

Lean 的标准库定义了两个谓词，``Acc r a`` 和 ``WellFounded r``，其中 ``r`` 是一个在类型 ``α`` 上的二元关系，而 ``a`` 是类型 ``α`` 的一个元素。

```lean
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)
```

<!--
The first, ``Acc``, is an inductively defined predicate. According to
its definition, ``Acc r x`` is equivalent to
``∀ y, r y x → Acc r y``. If you think of ``r y x`` as denoting a kind of order relation
``y ≺ x``, then ``Acc r x`` says that ``x`` is accessible from below,
in the sense that all its predecessors are accessible. In particular,
if ``x`` has no predecessors, it is accessible. Given any type ``α``,
we should be able to assign a value to each accessible element of
``α``, recursively, by assigning values to all its predecessors first.

The statement that ``r`` is well founded, denoted ``WellFounded r``,
is exactly the statement that every element of the type is
accessible. By the above considerations, if ``r`` is a well-founded
relation on a type ``α``, we should have a principle of well-founded
recursion on ``α``, with respect to the relation ``r``. And, indeed,
we do: the standard library defines ``WellFounded.fix``, which serves
exactly that purpose.
-->

首先 ``Acc`` 是一个归纳定义的谓词。根据定义，``Acc r x`` 等价于
``∀ y, r y x → Acc r y``。如果你把 ``r y x`` 考虑成一种序关系 ``y ≺ x``，那么 ``Acc r x`` 说明 ``x`` 在下文中可访问，
从某种意义上说，它的所有前继都是可访问的。特别地，如果 ``x`` 没有前继，它是可访问的。给定任何类型 ``α``，我们应该能够通过首先为 ``α`` 的所有前继元素赋值，递归地为 ``α`` 的每个可访问元素赋值。

使用 ``WellFounded r`` 来声明 ``r`` 是良基的，即说明该类型的每个元素都是可访问的。根据上述考虑，如果 ``r`` 是类型 ``α`` 上的一个成立良好的关系，那么对于关系 ``r``，我们应该有一个关于 ``α`` 的成立良好的递归原则。确实，我们这样做了：标准库定义了 ``WellFounded.fix``，它正好满足这个目的。

```lean
noncomputable def f {α : Sort u}
      (r : α → α → Prop)
      (h : WellFounded r)
      (C : α → Sort v)
      (F : (x : α) → ((y : α) → r y x → C y) → C x)
      : (x : α) → C x := WellFounded.fix h F
```

<!--
There is a long cast of characters here, but the first block we have
already seen: the type, ``α``, the relation, ``r``, and the
assumption, ``h``, that ``r`` is well founded. The variable ``C``
represents the motive of the recursive definition: for each element
``x : α``, we would like to construct an element of ``C x``. The
function ``F`` provides the inductive recipe for doing that: it tells
us how to construct an element ``C x``, given elements of ``C y`` for
each predecessor ``y`` of ``x``.

Note that ``WellFounded.fix`` works equally well as an induction
principle. It says that if ``≺`` is well founded and you want to prove
``∀ x, C x``, it suffices to show that for an arbitrary ``x``, if we
have ``∀ y ≺ x, C y``, then we have ``C x``.

In the example above we use the modifier `noncomputable` because the code
generator currently does not support `WellFounded.fix`. The function
`WellFounded.fix` is another tool Lean uses to justify that a function
terminates.

Lean knows that the usual order ``<`` on the natural numbers is well
founded. It also knows a number of ways of constructing new well
founded orders from others, for example, using lexicographic order.

Here is essentially the definition of division on the natural numbers that is found in the standard library.
-->

这里有一大堆字，但我们熟悉第一块：类型 ``α``，关系 ``r`` 和假设 ``h``，即 ``r`` 是有良基的。变量' ``C`` 代表递归定义的动机：对于每个元素 ``x : α``，我们想构造一个 ``C x`` 的元素。函数 ``F`` 提供了这样做的归纳方法：它告诉我们如何构造一个元素 ``C x``，给定 ``C y`` 的元素对于 ``x`` 的每个 ``y``。

注意 ``WellFounded.fix`` 和归纳法原理一样有效。它说如果 ``≺`` 是良基的，而你想要证明 ``∀ x, C x``，那么只要证明对于任意的 ``x``，如果我们有 ``∀ y ≺ x, C y``，那么我们就有 ``C x`` 就足够了。

在上面的例子中，我们使用了修饰符 `noncomputable`，因为代码生成器目前不支持 `WellFounded.fix`。函数 `WellFounded.fix` 是 Lean 用来证明函数终止的另一个工具。

Lean 知道自然数上通常的序 ``<`` 是良基的。它还知道许多从其他东西中构造新的良基的序的方法，例如字典序。

下面是标准库中自然数除法的定义。

```lean
open Nat

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_lemma h) y + 1
  else
    zero

noncomputable def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2 -- 4
```

<!--
The definition is somewhat inscrutable. Here the recursion is on
``x``, and ``div.F x f : Nat → Nat`` returns the "divide by ``y``"
function for that fixed ``x``. You have to remember that the second
argument to ``div.F``, the recipe for the recursion, is a function
that is supposed to return the divide by ``y`` function for all values
``x₁`` smaller than ``x``.

The elaborator is designed to make definitions like this more
convenient. It accepts the following:
-->

这个定义有点难以理解。这里递归在 ``x`` 上， ``div.F x f : Nat → Nat`` 为固定的 ``x`` 返回「除以 ``y``」函数。你要记住 ``div.F`` 的第二个参数 ``f`` 是递归的具体实现，这个函数对所有小于 ``x`` 的自然数 ``x₁`` 返回「除以 ``y``」函数。

繁饰器（Elaborator）可以使这样的定义更加方便。它接受下列内容:

```lean
def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div (x - y) y + 1
  else
    0
```

<!--
When Lean encounters a recursive definition, it first
tries structural recursion, and only when that fails, does it fall
back on well-founded recursion. Lean uses the tactic `decreasing_tactic`
to show that the recursive applications are smaller. The auxiliary
proposition `x - y < x` in the example above should be viewed as a hint
for this tactic.

The defining equation for ``div`` does *not* hold definitionally, but
we can unfold `div` using the `unfold` tactic. We use [`conv`](./conv.md) to select which
`div` application we want to unfold.
-->

当 Lean 遇到递归定义时，它首先尝试结构递归，失败时才返回到良基递归。Lean 使用 `decreasing_tactic` 来显示递归应用会越来越小。上面例子中的辅助命题 `x - y < x` 应该被视为这种策略的提示。

``div`` 的定义公式不具有定义性，但我们可以使用 `unfold` 策略展开 ``div``。我们使用 [`conv`](./conv.md) 来选择要展开的 ``div`` 应用。

<!--
```lean
# def div (x y : Nat) : Nat :=
#  if h : 0 < y ∧ y ≤ x then
#    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
#    div (x - y) y + 1
#  else
#    0
example (x y : Nat) : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 := by
  conv => lhs; unfold div -- unfold occurrence in the left-hand-side of the equation

example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]
```
-->

```lean
# def div (x y : Nat) : Nat :=
#  if h : 0 < y ∧ y ≤ x then
#    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
#    div (x - y) y + 1
#  else
#    0
example (x y : Nat) : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 := by
  conv => lhs; unfold div -- 展开方程左侧的div

example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]
```

<!--
The following example is similar: it converts any natural number to a
binary expression, represented as a list of 0's and 1's. We have to
provide evidence that the recursive call is
decreasing, which we do here with a ``sorry``. The ``sorry`` does not
prevent the interpreter from evaluating the function successfully.
-->

下面的示例与此类似：它将任何自然数转换为二进制表达式，表示为0和1的列表。我们必须提供递归调用正在递减的证据，我们在这里用 ``sorry`` 来做。``sorry`` 并不会阻止解释器成功地对函数求值。

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2]

#eval natToBin 1234567
```

<!--
As a final example, we observe that Ackermann's function can be
defined directly, because it is justified by the well foundedness of
the lexicographic order on the natural numbers. The `termination_by` clause
instructs Lean to use a lexicographic order. This clause is actually mapping
the function arguments to elements of type `Nat × Nat`. Then, Lean uses typeclass
resolution to synthesize an element of type `WellFoundedRelation (Nat × Nat)`.
-->

最后一个例子，我们观察到Ackermann函数可以直接定义，因为它可以被自然数上字典序的良基性证明。`termination_by` 子句指示 Lean 使用字典序。这个子句实际上是将函数参数映射到类型为 `Nat × Nat` 的元素。然后，Lean 使用类型类解析来合成类型为 `WellFoundedRelation (Nat × Nat)` 的元素。

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
```

<!--
Note that a lexicographic order is used in the example above because the instance
`WellFoundedRelation (α × β)` uses a lexicographic order. Lean also defines the instance
-->

注意，在上面的例子中使用了字典序，因为实例 `WellFoundedRelation (α × β)` 使用了字典序。Lean 还定义了实例

```lean
instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel
```

<!--
In the following example, we prove termination by showing that `as.size - i` is decreasing
in the recursive application.
-->

在下面的例子中，我们通过显示 `as.size - i` 在递归应用中是递减的来证明它会终止。

```lean
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as.get ⟨i, h⟩
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
  termination_by as.size - i
```

<!--
Note that, auxiliary function `go` is recursive in this example, but `takeWhile` is not.

By default, Lean uses the tactic `decreasing_tactic` to prove recursive applications are decreasing. The modifier `decreasing_by` allows us to provide our own tactic. Here is an example.
-->

注意，辅助函数 `go` 在这个例子中是递归的，但 `takeWhile` 不是。

默认情况下，Lean 使用 `decreasing_tactic` 来证明递归应用正在递减。修饰词 `decreasing_by` 允许我们提供自己的策略。这里有一个例子。

```lean
theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div (x - y) y + 1
  else
    0
decreasing_by apply div_lemma; assumption
```

<!--
Note that `decreasing_by` is not replacement for `termination_by`, they complement each other. `termination_by` is used to specify a well-founded relation, and `decreasing_by` for providing our own tactic for showing recursive applications are decreasing. In the following example, we use both of them.
-->

注意 `decreasing_by` 不是 `termination_by` 的替代，它们是互补的。 `termination_by` 用于指定一个良基关系， `decreasing_by` 用于提供我们自己的策略来显示递归应用正在递减。在下面的示例中，我们将同时使用它们。

<!--
```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
decreasing_by
  all_goals simp_wf -- unfolds well-founded recursion auxiliary definitions
  · apply Prod.Lex.left; simp_arith
  · apply Prod.Lex.right; simp_arith
  · apply Prod.Lex.left; simp_arith
```

-->

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
decreasing_by
  all_goals simp_wf -- 展开良基的递归辅助定义
  · apply Prod.Lex.left; simp_arith
  · apply Prod.Lex.right; simp_arith
  · apply Prod.Lex.left; simp_arith
```

<!--
We can use `decreasing_by sorry` to instruct Lean to "trust" us that the function terminates.
-->

我们可以使用 `decreasing_by sorry` 来指示 Lean 「相信」函数可以终止。

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 => natToBin ((n + 2) / 2) ++ [n % 2]
decreasing_by sorry

#eval natToBin 1234567
```

<!--
Recall that using `sorry` is equivalent to using a new axiom, and should be avoided. In the following example, we used the `sorry` to prove `False`. The command `#print axioms` shows that `unsound` depends on the unsound axiom `sorryAx` used to implement `sorry`.
-->

回想一下，使用 `sorry` 相当于使用一个新的公理，应该避免使用。在下面的例子中，我们用 `sorry` 来证明 `False`。命令 `#print axioms` 显示，`unsound` 依赖于用于实现 `sorry` 的不健全公理 `sorryAx`。

<!--
```lean
def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
-- `unsound 0` is a proof of `False`

#print axioms unsound
-- 'unsound' depends on axioms: [sorryAx]
```
-->

```lean
def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
-- `unsound 0` 是 `False` 的一个证明

#print axioms unsound
-- 'unsound' 依赖于公理：[sorryAx]
```

<!--
Summary:

- If there is no `termination_by`, a well-founded relation is derived (if possible) by selecting an argument and then using typeclass resolution to synthesize a well-founded relation for this argument's type.

- If `termination_by` is specified, it maps the arguments of the function to a type `α` and type class resolution is again used. Recall that, the default instance for `β × γ` is a lexicographic order based on the well-founded relations for `β` and `γ`.

- The default well-founded relation instance for `Nat` is `<`.

- By default, the tactic `decreasing_tactic` is used to show that recursive applications are smaller with respect to the selected well-founded relation. If `decreasing_tactic` fails, the error message includes the remaining goal `... |- G`. Note that, the `decreasing_tactic` uses `assumption`. So, you can include a `have`-expression to prove goal `G`. You can also provide your own tactic using `decreasing_by`.
-->

总结：

- 如果没有 `termination_by`，良基关系（可能）可以这样被导出：选择一个参数，然后使用类型类解析为该参数的类型合成一个良基关系。

- 如果指定了 `termination_by`，它将函数的参数映射为类型 `α`，并再次使用类型类解析。 回想一下，`β × γ` 的默认实例是基于 `β` 和 `γ`的良基关系的字典序。
-
- `Nat` 的默认良基关系实例是 `<`。

- 默认情况下，策略 `decreasing_tactic` 用于显示递归应用小于选择的良基关系。如果 `decreasing_tactic` 失败，错误信息包括剩余目标 `... |- G`。注意，`decreasing_tactic` 使用 `assumption`。所以，你可以用 `have` 表达式来证明目标 `G`。你也可以使用 `decreasing_by` 来提供你自己的策略。

<!--
Mutual Recursion
-->

相互递归
----------------

<!--
Lean also supports mutual recursive definitions. The syntax is similar to that for mutual inductive types. Here is an example:
-->

Lean 还提供相互递归定义，语法类似相互归纳类型。例子：

```lean
mutual
  def even : Nat → Bool
    | 0   => true
    | n+1 => odd n

  def odd : Nat → Bool
    | 0   => false
    | n+1 => even n
end

example : even (a + 1) = odd a := by
  simp [even]

example : odd (a + 1) = even a := by
  simp [odd]

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a; induction a
  . simp [even, odd]
  . simp [even, odd, *]
```

这是一个相互的定义，因为 ``even`` 是用 ``odd`` 递归定义的，而 ``odd`` 是用 ``even`` 递归定义的。在底层，它被编译为单个递归定义。内部定义的函数接受sum类型的元素作为参数，可以是 ``even`` 的输入，也可以是 ``odd`` 的输入。然后，它返回与输入相适应的输出。为了定义这个功能，Lean 使用了一个合适的、良基的度量。内部是对用户隐藏的；使用这些定义的规范方法是使用 ``simp`` （或 `unfold`），正如我们上面所做的那样。

相互递归定义还提供了处理相互和嵌套归纳类型的自然方法。回想一下前面提到的 ``Even`` 和 ``Odd`` 作为相互归纳谓词的定义。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end
```

<!--
The constructors, ``even_zero``, ``even_succ``, and ``odd_succ`` provide positive means for showing that a number is even or odd. We need to use the fact that the inductive type is generated by these constructors to know that zero is not odd, and that the latter two implications reverse. As usual, the constructors are kept in a namespace that is named after the type being defined, and the command ``open Even Odd`` allows us to access them more conveniently.
-->

构造子 ``even_zero``、``even_succ`` 和 ``odd_succ`` 提供了显示数字是偶数还是奇数的积极方法。我们需要利用归纳类型是由这些构造子生成的这一事实来知道零不是奇数，并且后两个含义是相反的。像往常一样，构造子保存在以定义的类型命名的命名空间中，并且命令 ``open Even Odd`` 允许我们更方便地访问它们。

```lean
# mutual
#  inductive Even : Nat → Prop where
#    | even_zero : Even 0
#    | even_succ : ∀ n, Odd n → Even (n + 1)
#  inductive Odd : Nat → Prop where
#    | odd_succ : ∀ n, Even n → Odd (n + 1)
# end
open Even Odd

theorem not_odd_zero : ¬ Odd 0 :=
  fun h => nomatch h

theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
  | _, odd_succ n h => h

theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
  | _, even_succ n h => h
```

<!--
For another example, suppose we use a nested inductive type to define a set of terms inductively, so that a term is either a constant (with a name given by a string), or the result of applying a constant to a list of constants.
-->

另一个例子，假设我们使用嵌套归纳类型来归纳定义一组项，这样，项要么是常量(由字符串给出名称)，要么是将常量应用于常量列表的结果。

```lean
inductive Term where
  | const : String → Term
  | app   : String → List Term → Term
```

<!--
We can then use a mutual recursive definition to count the number of constants occurring in a term, as well as the number occurring in a list of terms.
-->

然后，我们可以使用一个相互递归的定义来计算在一个项中出现的常量的数量，以及在一个项列表中出现的常量的数量。

```lean
# inductive Term where
#  | const : String → Term
#  | app   : String → List Term → Term
namespace Term

mutual
  def numConsts : Term → Nat
    | const _ => 1
    | app _ cs => numConstsLst cs

  def numConstsLst : List Term → Nat
    | [] => 0
    | c :: cs => numConsts c + numConstsLst cs
end

def sample := app "f" [app "g" [const "x"], const "y"]

#eval numConsts sample

end Term
```

<!--
As a final example, we define a function `replaceConst a b e` that replaces a constant `a` with `b` in a term `e`, and then prove the number of constants is the same. Note that, our proof uses mutual recursion (aka induction).
-->

作为最后一个例子，我们定义了一个函数 `replaceConst a b e`，它将项 `e` 中的常数 `a` 替换为 `b`，然后证明常数的数量是相同的。注意，我们的证明使用了相互递归（即归纳法）。

```lean
# inductive Term where
#  | const : String → Term
#  | app   : String → List Term → Term
# namespace Term
# mutual
#  def numConsts : Term → Nat
#    | const _ => 1
#    | app _ cs => numConstsLst cs
#   def numConstsLst : List Term → Nat
#    | [] => 0
#    | c :: cs => numConsts c + numConstsLst cs
# end
mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)

  def replaceConstLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end

mutual
  theorem numConsts_replaceConst (a b : String) (e : Term)
            : numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c => simp [replaceConst]; split <;> simp [numConsts]
    | app f cs => simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]

  theorem numConsts_replaceConstLst (a b : String) (es : List Term)
            : numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | [] => simp [replaceConstLst, numConstsLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
            numConsts_replaceConstLst a b cs]
end
```

<!--
Dependent Pattern Matching
--------------------------
-->

依值模式匹配
--------------------------

<!--
All the examples of pattern matching we considered in
[Section Pattern Matching](#pattern-matching) can easily be written using ``casesOn``
and ``recOn``. However, this is often not the case with indexed
inductive families such as ``Vector α n``, since case splits impose
constraints on the values of the indices. Without the equation
compiler, we would need a lot of boilerplate code to define very
simple functions such as ``map``, ``zip``, and ``unzip`` using
recursors. To understand the difficulty, consider what it would take
to define a function ``tail`` which takes a vector
``v : Vector α (succ n)`` and deletes the first element. A first thought might be to
use the ``casesOn`` function:
-->

我们在[模式匹配](#模式匹配)一节中考虑的所有模式匹配示例都可以很容易地使用 ``casesOn`` 和 ``recOn`` 来编写。然而，对于索引归纳族，如 ``Vector α n``，通常不是这种情况，因为区分情况要对索引的值施加约束。如果没有方程编译器，我们将需要大量的样板代码来定义非常简单的函数，例如使用递归定义 ``map``、``zip`` 和 ``unzip``。为了理解其中的困难，考虑一下如何定义一个函数 ``tail``，它接受一个向量 ``v : Vector α (succ n)`` 并删除第一个元素。首先想到的可能是使用 ``casesOn`` 函数:

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

#check @Vector.casesOn
/-
  {α : Type u}
  → {motive : (a : Nat) → Vector α a → Sort v} →
  → {a : Nat} → (t : Vector α a)
  → motive 0 nil
  → ((a : α) → {n : Nat} → (a_1 : Vector α n) → motive (n + 1) (cons a a_1))
  → motive a t
-/

end Vector
```

<!--
But what value should we return in the ``nil`` case? Something funny
is going on: if ``v`` has type ``Vector α (succ n)``, it *can't* be
nil, but it is not clear how to tell that to ``casesOn``.

One solution is to define an auxiliary function:
-->

但是在 ``nil`` 的情况下我们应该返回什么值呢？有趣的事情来了：如果 ``v`` 具有 ``Vector α (succ n)`` 类型，它「不能」为nil，但很难告诉 ``casesOn``。

一种解决方案是定义一个辅助函数:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn (motive := fun x _ => x = n + 1 → Vector α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl
# end Vector
```

<!--
In the ``nil`` case, ``m`` is instantiated to ``0``, and
``noConfusion`` makes use of the fact that ``0 = succ n`` cannot
occur.  Otherwise, ``v`` is of the form ``a :: w``, and we can simply
return ``w``, after casting it from a vector of length ``m`` to a
vector of length ``n``.

The difficulty in defining ``tail`` is to maintain the relationships between the indices.
The hypothesis ``e : m = n + 1`` in ``tailAux`` is used to communicate the relationship
between ``n`` and the index associated with the minor premise.
Moreover, the ``zero = n + 1`` case is unreachable, and the canonical way to discard such
a case is to use ``noConfusion``.

The ``tail`` function is, however, easy to define using recursive
equations, and the equation compiler generates all the boilerplate
code automatically for us. Here are a number of similar examples:
-->

在 ``nil`` 的情况下，``m`` 被实例化为 ``0``，``noConfusion`` 利用了 ``0 = succ n`` 不能出现的事实。否则，``v`` 的形式为 ``a :: w``，我们可以简单地将 ``w`` 从长度 ``m`` 的向量转换为长度 ``n`` 的向量后返回 ``w``。

定义 ``tail`` 的困难在于维持索引之间的关系。 ``tailAux`` 中的假设 ``e : m = n + 1`` 用于传达 ``n`` 与与小前提相关的索引之间的关系。此外，``zero = n + 1`` 的情况是不可达的，而放弃这种情况的规范方法是使用 ``noConfusion``。

然而，``tail`` 函数很容易使用递归方程来定义，并且方程编译器会自动为我们生成所有样板代码。下面是一些类似的例子:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : {n : Nat} → Vector α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vector α (n+1) → Vector α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vector α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : {n : Nat} → Vector α n → Vector β n → Vector (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

<!--
Note that we can omit recursive equations for "unreachable" cases such
as ``head nil``. The automatically generated definitions for indexed
families are far from straightforward. For example:
-->

注意，对于「不可达」的情况，例如 ``head nil``，我们可以省略递归方程。为索引族自动生成的定义远非直截了当。例如:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def map (f : α → β → γ) : {n : Nat} → Vector α n → Vector β n → Vector γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

#print map
#print map.match_1
# end Vector
```

<!--
The ``map`` function is even more tedious to define by hand than the
``tail`` function. We encourage you to try it, using ``recOn``,
``casesOn`` and ``noConfusion``.
-->

与 ``tail`` 函数相比，``map`` 函数手工定义更加繁琐。我们鼓励您尝试使用 ``recOn``、``casesOn`` 和 ``noConfusion``。

<!--
Inaccessible Patterns
------------------
-->

不可访问模式
------------------

<!--
Sometimes an argument in a dependent matching pattern is not essential
to the definition, but nonetheless has to be included to specialize
the type of the expression appropriately. Lean allows users to mark
such subterms as *inaccessible* for pattern matching. These
annotations are essential, for example, when a term occurring in the
left-hand side is neither a variable nor a constructor application,
because these are not suitable targets for pattern matching. We can
view such inaccessible patterns as "don't care" components of the
patterns. You can declare a subterm inaccessible by writing
``.(t)``. If the inaccessible pattern can be inferred, you can also write
``_``.

The following example, we declare an inductive type that defines the
property of "being in the image of ``f``". You can view an element of
the type ``ImageOf f b`` as evidence that ``b`` is in the image of
``f``, whereby the constructor ``imf`` is used to build such
evidence. We can then define any function ``f`` with an "inverse"
which takes anything in the image of ``f`` to an element that is
mapped to it. The typing rules forces us to write ``f a`` for the
first argument, but this term is neither a variable nor a constructor
application, and plays no role in the pattern-matching definition. To
define the function ``inverse`` below, we *have to* mark ``f a``
inaccessible.
-->

有时候，依值匹配模式中的参数对定义来说并不是必需的，但是必须包含它来适当地确定表达式的类型。Lean 允许用户将这些子项标记为「不可访问」以进行模式匹配。例如，当左侧出现的项既不是变量也不是构造子应用时，这些注解是必不可少的，因为它们不适合用于模式匹配的目标。我们可以将这种不可访问的模式视为模式的「不关心」组件。你可以通过写 ``.(t)`` 来声明子项不可访问。如果不可访问的模式可以被推断出来，你也可以写 ``_``。

下面的例子中，我们声明了一个归纳类型，它定义了「在 ``f`` 的像中」的属性。您可以将 ``ImageOf f b`` 类型的元素视为 ``b`` 位于 ``f`` 的像中的证据，构造子 ``imf`` 用于构建此类证据。然后，我们可以定义任何函数 ``f`` 的「逆」，逆函数将 ``f`` 的像中的任何元素赋给映射到它的元素。类型规则迫使我们为第一个参数写 ``f a``，但是这个项既不是变量也不是构造子应用，并且在模式匹配定义中没有作用。为了定义下面的函数 ``inverse``，我们必须将 ``f a`` 标记为不可访问。

```lean
inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a
```

<!--
In the example above, the inaccessible annotation makes it clear that
``f`` is *not* a pattern matching variable.

Inaccessible patterns can be used to clarify and control definitions that
make use of dependent pattern matching. Consider the following
definition of the function ``Vector.add``, which adds two vectors of
elements of a type, assuming that type has an associated addition
function:
-->

在上面的例子中，不可访问记号清楚地表明 ``f`` 不是一个模式匹配变量。

不可访问模式可用于澄清和控制使用依值模式匹配的定义。考虑函数 ``Vector.add`` 的以下定义，假设该类型有满足结合律的加法函数，它将一个类型的两个元素向量相加:

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

namespace Vector

def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)

end Vector
```

<!--
The argument ``{n : Nat}`` appear after the colon, because it cannot
be held fixed throughout the definition.  When implementing this
definition, the equation compiler starts with a case distinction as to
whether the first argument is ``0`` or of the form ``n+1``.  This is
followed by nested case splits on the next two arguments, and in each
case the equation compiler rules out the cases are not compatible with
the first pattern.

But, in fact, a case split is not required on the first argument; the
``casesOn`` eliminator for ``Vector`` automatically abstracts this
argument and replaces it by ``0`` and ``n + 1`` when we do a case
split on the second argument. Using inaccessible patterns, we can prompt
the equation compiler to avoid the case split on ``n``
-->

参数 ``{n : Nat}`` 出现在冒号之后，因为它不能在整个定义中保持固定。在实现这个定义时，方程编译器首先区分第一个参数是 ``0`` 还是 ``n+1``。对接下来的两个参数嵌套地区分情况，在每种情况下，方程编译器都会排除与第一个模式不兼容的情况。

但事实上，在第一个参数上不需要区分情况；当我们对第二个参数区分情况时，``Vector`` 的 ``casesOn`` 消去器会自动抽象该参数，并将其替换为 ``0`` 和 ``n + 1``。使用不可访问的模式，我们可以提示方程编译器不要在 ``n`` 上区分情况。

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | .(_), nil,       nil       => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

<!--
Marking the position as an inaccessible pattern tells the
equation compiler first, that the form of the argument should be
inferred from the constraints posed by the other arguments, and,
second, that the first argument should *not* participate in pattern
matching.

The inaccessible pattern `.(_)` can be written as `_` for convenience.
-->

将位置标记为不可访问模式首先告诉方程编译器，参数的形式应该从其他参数所构成的约束中推断出来，其次，第一个参数不应该参与模式匹配。

为简便起见，不可访问的模式 `.(_)` 可以写成 `_`。

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] : {n : Nat} → Vector α n → Vector α n → Vector α n
  | _, nil,       nil       => nil
  | _, cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

<!--
As we mentioned above, the argument ``{n : Nat}`` is part of the
pattern matching, because it cannot be held fixed throughout the
definition. In previous Lean versions, users often found it cumbersome
to have to include these extra discriminants. Thus, Lean 4
implements a new feature, *discriminant refinement*, which includes
these extra discriminants automatically for us.
-->

如前所述，参数 ``{n : Nat}`` 是模式匹配的一部分，因为它不能在整个定义中保持固定。在以前的 Lean 版本中，用户经常发现必须包含这些额外的判别符是很麻烦的。因此，Lean 4 实现了一个新特性， **判别精炼（discriminant refinement）** ，它自动为我们包含了这些额外的判别。

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] {n : Nat} : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

<!--
When combined with the *auto bound implicits* feature, you can simplify
the declare further and write:
-->

当与「自动绑定隐式」特性结合使用时，你可以进一步简化声明并这样写：

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def add [Add α] : Vector α n → Vector α n → Vector α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
# end Vector
```

<!--
Using these new features, you can write the other vector functions defined
in the previous sections more compactly as follows:
-->

使用这些新特性，您可以更紧凑地编写在前几节中定义的其他向量函数，如下所示:

```lean
# inductive Vector (α : Type u) : Nat → Type u
#   | nil  : Vector α 0
#   | cons : α → {n : Nat} → Vector α n → Vector α (n+1)
# namespace Vector
def head : Vector α (n+1) → α
  | cons a as => a

def tail : Vector α (n+1) → Vector α n
  | cons a as => as

theorem eta : (v : Vector α (n+1)) → cons (head v) (tail v) = v
  | cons a as => rfl

def map (f : α → β → γ) : Vector α n → Vector β n → Vector γ n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : Vector α n → Vector β n → Vector (α × β) n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a, b) (zip as bs)
# end Vector
```

<!--
Match Expressions
-----------------
-->

Match 表达式
-----------------

<!--
Lean also provides a compiler for *match-with* expressions found in
many functional languages.
-->

Lean 还提供「match-with」表达式，它在很多函数式语言中都能找到。

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true
```

<!--
This does not look very different from an ordinary pattern matching
definition, but the point is that a ``match`` can be used anywhere in
an expression, and with arbitrary arguments.
-->

这看起来与普通的模式匹配定义没有太大的不同，但关键是 ``match`` 可以在表达式中的任何地方使用，并带有任意参数。

```lean
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0   => false
  | n+1 => true

def filter (p : α → Bool) : List α → List α
  | []      => []
  | a :: as =>
    match p a with
    | true => a :: filter p as
    | false => filter p as

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl
```

<!--
Here is another example:
-->

另一例：

```lean
def foo (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,   true  => 0
      | m+1, true  => m + 7
      | 0,   false => 5
      | m+1, false => m + 3

#eval foo 7 true false

example : foo 7 true false = 9 := rfl
```

<!--
Lean uses the ``match`` construct internally to implement pattern-matching in all parts of the system.
Thus, all four of these definitions have the same net effect.
-->

Lean 使用内建的 ``match`` 来实现系统所有地方的模式匹配。因此，这四种定义具有相同的净效果。

```lean
def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n
```

<!--
These variations are equally useful for destructing propositions:
-->

这些变体在解构命题中也是同样有用的：

```lean
variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
        : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩
```

<!--
Local Recursive Declarations
---------
-->

局域递归声明
---------

<!--
You can define local recursive declarations using the `let rec` keyword.
-->

可以通过 `let rec` 关键字定义局域递归声明。

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α
```

<!--
Lean creates an auxiliary declaration for each `let rec`. In the example above,
it created the declaration `replicate.loop` for the `let rec loop` occurring at `replicate`.
Note that, Lean "closes" the declaration by adding any local variable occurring in the
`let rec` declaration as additional parameters. For example, the local variable `a` occurs
at `let rec loop`.

You can also use `let rec` in tactic mode and for creating proofs by induction.
-->

Lean 对每个 `let rec`创建一个辅助声明。上例中，它为出现在 `replicate` 中的 `let rec loop` 创建了一个声明 `replicate.loop`。注意到，Lean 通过添加任意的出现在 `let rec` 声明中的局域变量作为附加参数来「关闭」声明。例如，局域变量 `a` 出现在 `let rec loop` 当中。

也在策略模式中可使用 `let rec` 来建立归纳证明。

```lean
# def replicate (n : Nat) (a : α) : List α :=
#  let rec loop : Nat → List α → List α
#    | 0,   as => as
#    | n+1, as => loop n (a::as)
#  loop n []
theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
  exact aux n []
```

<!--
You can also introduce auxiliary recursive declarations using a `where` clause after your definition.
Lean converts them into a `let rec`.
-->

也可以用 `where` 语句在定义后面引入辅助递归声明，Lean 自动把它们转译成 `let rec`。

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp [replicate.loop, aux n, Nat.add_succ, Nat.succ_add]
```

<!--
Exercises
---------
-->

练习
---------

<!--
1. Open a namespace ``Hidden`` to avoid naming conflicts, and use the
   equation compiler to define addition, multiplication, and
   exponentiation on the natural numbers. Then use the equation
   compiler to derive some of their basic properties.

2. Similarly, use the equation compiler to define some basic
   operations on lists (like the ``reverse`` function) and prove
   theorems about lists by induction (such as the fact that
   ``reverse (reverse xs) = xs`` for any list ``xs``).

3. Define your own function to carry out course-of-value recursion on
   the natural numbers. Similarly, see if you can figure out how to
   define ``WellFounded.fix`` on your own.

4. Following the examples in [Section Dependent Pattern Matching](#dependent-pattern-matching),
   define a function that will append two vectors.
   This is tricky; you will have to define an auxiliary function.

5. Consider the following type of arithmetic expressions. The idea is
   that ``var n`` is a variable, ``vₙ``, and ``const n`` is the
   constant whose value is ``n``.
-->

1. 打开命名空间 ``Hidden`` 以避免命名冲突，并使用方程编译器定义自然数的加法、乘法和幂运算。然后用方程编译器派生出它们的一些基本属性。

2. 类似地，使用方程编译器定义列表上的一些基本操作(如 ``reverse`` 函数)，并通过归纳法证明关于列表的定理（例如对于任何列表 ``xs``，``reverse (reverse xs) = xs`` ）。

3. 定义您自己的函数来对自然数执行值的过程递归。同样，看看你是否能弄清楚如何定义 ``WellFounded.fix``。

4. 按照[依值模式匹配](#依值模式匹配)中的例子，定义一个追加（append）两个向量的函数。提示：你必须定义一个辅助函数。

5. 考虑以下类型的算术表达式。这个想法是，``var n`` 是一个变量 ``vₙ``，``const n`` 是一个常量，它的值是 ``n``。

```lean
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))
```

<!--
Here ``sampleExpr`` represents ``(v₀ * 7) + (2 * v₁)``.

Write a function that evaluates such an expression, evaluating each ``var n`` to ``v n``.
-->

此处 ``sampleExpr`` 表示 ``(v₀ * 7) + (2 * v₁)``。

写一个函数来计算这些表达式，对每个 ``var n`` 赋值 ``v n``.

<!--
```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def sampleExpr : Expr :=
#   plus (times (var 0) (const 7)) (times (const 2) (var 1))
def eval (v : Nat → Nat) : Expr → Nat
  | const n     => sorry
  | var n       => v n
  | plus e₁ e₂  => sorry
  | times e₁ e₂ => sorry

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- Try it out. You should get 47 here.
-- #eval eval sampleVal sampleExpr
```
-->

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def sampleExpr : Expr :=
#   plus (times (var 0) (const 7)) (times (const 2) (var 1))
def eval (v : Nat → Nat) : Expr → Nat
  | const n     => sorry
  | var n       => v n
  | plus e₁ e₂  => sorry
  | times e₁ e₂ => sorry

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- 如果答案是47说明你写的对。
-- #eval eval sampleVal sampleExpr
```

<!--
Implement "constant fusion," a procedure that simplifies subterms like
``5 + 7`` to ``12``. Using the auxiliary function ``simpConst``,
define a function "fuse": to simplify a plus or a times, first
simplify the arguments recursively, and then apply ``simpConst`` to
try to simplify the result.
-->

实现「常数融合」，这是一个将 ``5 + 7`` 等子术语化简为 ``12`` 的过程。使用辅助函数 ``simpConst``，定义一个函数「fuse」:为了化简加号或乘号，首先递归地化简参数，然后应用 ``simpConst`` 尝试化简结果。

```lean
# inductive Expr where
#   | const : Nat → Expr
#   | var : Nat → Expr
#   | plus : Expr → Expr → Expr
#   | times : Expr → Expr → Expr
#   deriving Repr
# open Expr
# def eval (v : Nat → Nat) : Expr → Nat
#   | const n     => sorry
#   | var n       => v n
#   | plus e₁ e₂  => sorry
#   | times e₁ e₂ => sorry
def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr := sorry

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry
```

<!--
The last two theorems show that the definitions preserve the value.
-->

最后两个定理表明，定义保持值不变。
