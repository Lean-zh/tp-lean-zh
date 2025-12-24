import VersoManual
import TPiLZh.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiLZh

set_option linter.typography.dashes false

#doc (Manual) "归纳和递归" =>
%%%
tag := "induction-and-recursion"
file := "InductionAndRecursion"
%%%
-- Induction and Recursion

-- In the previous chapter, we saw that inductive definitions provide a
-- powerful means of introducing new types in Lean. Moreover, the
-- constructors and the recursors provide the only means of defining
-- functions on these types. By the {tech}[propositions-as-types] correspondence,
-- this means that induction is the fundamental method of proof.

在上一章中，我们看到归纳定义提供了在 Lean 中引入新类型的强大手段。此外，
构造子和递归器提供了在这些类型上定义函数的唯一手段。根据 {tech}[propositions-as-types] 对应关系，
这意味着归纳法是证明的基本方法。

-- Lean provides natural ways of defining recursive functions, performing
-- pattern matching, and writing inductive proofs. It allows you to
-- define a function by specifying equations that it should satisfy, and
-- it allows you to prove a theorem by specifying how to handle various
-- cases that can arise. Behind the scenes, these descriptions are
-- “compiled” down to primitive recursors, using a procedure that we
-- refer to as the “equation compiler.” The equation compiler is not part
-- of the trusted code base; its output consists of terms that are
-- checked independently by the kernel.

Lean 提供了定义递归函数、执行模式匹配和编写归纳证明的自然方法。它允许你通过指定它应该满足的方程来定义一个函数，
它允许你通过指定如何处理可能出现的各种情况来证明一个定理。在它内部，这些描述被“编译”成原始递归器，
使用一个我们称之为“方程编译器”的程序。方程编译器不是可信代码库的一部分；它的输出包括由内核独立检查的项。

-- # Pattern Matching
# 模式匹配
%%%
tag := "pattern-matching"
%%%

-- The interpretation of schematic patterns is the first step of the
-- compilation process. We have seen that the {lit}`casesOn` recursor can
-- be used to define functions and prove theorems by cases, according to
-- the constructors involved in an inductively defined type. But
-- complicated definitions may use several nested {lit}`casesOn`
-- applications, and may be hard to read and understand. Pattern matching
-- provides an approach that is more convenient, and familiar to users of
-- functional programming languages.

对示意图模式的解释是编译过程的第一步。我们已经看到，{lit}`casesOn` 递归器可以通过分情况讨论来定义函数和证明定理，
根据归纳定义类型所涉及的构造子。但是复杂的定义可能会使用几个嵌套的 {lit}`casesOn` 应用，
而且可能很难阅读和理解。模式匹配提供了一种更方便的方法，并且为函数式编程语言的用户所熟悉。

:::setup
```
open Nat
variable (x : Nat)
```

-- Consider the inductively defined type of natural numbers. Every
-- natural number is either {lean}`zero` or {lean}`succ x`, and so you can define
-- a function from the natural numbers to an arbitrary type by specifying
-- a value in each of those cases:

考虑一下自然数的归纳定义类型。每个自然数要么是 {lean}`zero`，要么是 {lean}`succ x`，
因此你可以通过在每个情况下指定一个值来定义一个从自然数到任意类型的函数：
:::

```lean
set_option linter.unusedVariables false
--------
open Nat

def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x

def isZero : Nat → Bool
  | zero   => true
  | succ x => false
```

-- The equations used to define these functions hold definitionally:

用来定义这些函数的方程在定义上是成立的：

```lean
open Nat
def sub1 : Nat → Nat
  | zero   => zero
  | succ x => x
def isZero : Nat → Bool
  | zero   => true
  | succ x => false
------
example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl
```

-- Instead of {leanRef}`zero` and {leanRef}`succ`, we can use more familiar notation:

我们可以用一些更耳熟能详的符号，而不是 {leanRef}`zero` 和 {leanRef}`succ`：

```lean
set_option linter.unusedVariables false
--------
def sub1 : Nat → Nat
  | 0     => 0
  | x + 1 => x

def isZero : Nat → Bool
  | 0     => true
  | x + 1 => false
```

-- Because addition and the zero notation have been assigned the
-- {attr}`[match_pattern]` attribute, they can be used in pattern matching. Lean
-- simply normalizes these expressions until the constructors {leanRef}`zero`
-- and {leanRef}`succ` are exposed.

因为加法和零符号已经被赋予 {attr}`[match_pattern]` 属性，它们可以被用于模式匹配。Lean 简单地将这些表达式规范化，
直到显示构造子 {leanRef}`zero` 和 {leanRef}`succ`。

-- Pattern matching works with any inductive type, such as products and option types:

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

-- Here we use it not only to define a function, but also to carry out a
-- proof by cases:

在这里，我们不仅用它来定义一个函数，而且还用它来进行逐情况证明：

```lean
namespace Hidden
------
def not : Bool → Bool
  | true  => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true  => show not (not true) = true from rfl
  | false => show not (not false) = false from rfl
------
end Hidden
```

-- Pattern matching can also be used to destruct inductively defined propositions:

模式匹配也可以用来解构归纳定义的命题：

```lean
example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq
```

-- This provides a compact way of unpacking hypotheses that make use of logical connectives.

这样解决带逻辑连接词的命题就很紧凑。

-- In all these examples, pattern matching was used to carry out a single
-- case distinction. More interestingly, patterns can involve nested
-- constructors, as in the following examples.

在所有这些例子中，模式匹配被用来进行单一情况的区分。更有趣的是，模式可以涉及嵌套的构造子，如下面的例子。

```lean
def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x
```

-- The equation compiler first splits on cases as to whether the input is
-- {leanRef}`zero` or of the form {leanRef}`succ x`.  It then does a case split on
-- whether {leanRef}`x` is of the form {leanRef}`zero` or {leanRef}`succ x`.  It determines
-- the necessary case splits from the patterns that are presented to it,
-- and raises an error if the patterns fail to exhaust the cases. Once
-- again, we can use arithmetic notation, as in the version below. In
-- either case, the defining equations hold definitionally.

方程编译器首先对输入是 {leanRef}`zero` 还是 {leanRef}`succ x` 的形式进行分类讨论，然后对 {leanRef}`x` 是 {leanRef}`zero` 还是 {leanRef}`succ x` 的形式进行分类讨论。
它从提交给它的模式中确定必要的情况拆分，如果模式不能穷尽情况，则会引发错误。同时，我们可以使用算术符号，如下面的版本。
在任何一种情况下，定义方程都是成立的。

```lean
def sub2 : Nat → Nat
  | 0   => 0
  | 1   => 0
  | x+2 => x
------
example : sub2 0 = 0 := rfl
example : sub2 1 = 0 := rfl
example : sub2 (x+2) = x := rfl

example : sub2 5 = 3 := rfl
```

:::setup
```
def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x
```
-- You can write {leanCommand}`#print sub2` to see how the function was compiled to
-- recursors. (Lean will tell you that {leanRef}`sub2` has been defined in terms
-- of an internal auxiliary function, {lean}`sub2.match_1`, but you can print
-- that out too.) Lean uses these auxiliary functions to compile {kw}`match` expressions.
-- Actually, the definition above is expanded to

你可以写 {leanCommand}`#print sub2` 来看看这个函数是如何被编译成递归器的。（Lean 会告诉你 {leanRef}`sub2` 已经被定义为内部辅助函数 {lean}`sub2.match_1`，
但你也可以把它打印出来）。Lean 使用这些辅助函数来编译 {kw}`match` 表达式。实际上，上面的定义被扩展为
:::
```lean
def sub2 : Nat → Nat :=
  fun x =>
    match x with
    | 0     => 0
    | 1     => 0
    | x + 2 => x
```

-- Here are some more examples of nested pattern matching:

下面是一些嵌套模式匹配的例子：

```lean
set_option linter.unusedVariables false
--------
example (p q : α → Prop) :
        (∃ x, p x ∨ q x) →
        (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

def foo : Nat × Nat → Nat
  | (0, n)     => 0
  | (m+1, 0)   => 1
  | (m+1, n+1) => 2
```

-- The equation compiler can process multiple arguments sequentially. For
-- example, it would be more natural to define the previous example as a
-- function of two arguments:

方程编译器可以按顺序处理多个参数。例如，将前面的例子定义为两个参数的函数会更自然：

```lean
set_option linter.unusedVariables false
--------
def foo : Nat → Nat → Nat
  | 0,     n     => 0
  | m + 1, 0     => 1
  | m + 1, n + 1 => 2
```

-- Here is another example:

另一例：

```lean
set_option linter.unusedVariables false
--------
def bar : List Nat → List Nat → Nat
  | [],      []      => 0
  | a :: as, []      => a
  | [],      b :: bs => b
  | a :: as, b :: bs => a + b
```

-- Note that the patterns are separated by commas.

这些模式是由逗号分隔的。

-- In each of the following examples, splitting occurs on only the first
-- argument, even though the others are included among the list of
-- patterns.

在下面的每个例子中，尽管其他参数包括在模式列表中，但只对第一个参数进行了分割。

```lean
set_option linter.unusedVariables false
namespace Hidden
------
def and : Bool → Bool → Bool
  | true,  a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | true,  _ => true
  | false, a => a

def cond : Bool → α → α → α
  | true,  x, y => x
  | false, x, y => y
------
end Hidden
```

-- Notice also that, when the value of an argument is not needed in the
-- definition, you can use an underscore instead. This underscore is
-- known as a _wildcard pattern_, or an _anonymous variable_. In contrast
-- to usage outside the equation compiler, here the underscore does _not_
-- indicate an implicit argument. The use of underscores for wildcards is
-- common in functional programming languages, and so Lean adopts that
-- notation. The section on {ref "wildcards-and-overlapping-patterns"}[wildcards and overlapping patterns]
-- expands on the notion of a wildcard, and the description of {ref "inaccessible-patterns"}[inaccessible patterns] explains how
-- you can use implicit arguments in patterns as well.

还要注意的是，当定义中不需要一个参数的值时，你可以用下划线来代替。这个下划线被称为 *通配符模式* ，或 *匿名变量* 。与方程编译器之外的用法不同，这里的下划线 *并不* 表示一个隐参数。使用下划线表示通配符在函数式编程语言中是很常见的，所以 Lean 采用了这种符号。{ref "wildcards-and-overlapping-patterns"}[通配符和重叠模式]一节阐述了通配符的概念，而{ref "inaccessible-patterns"}[不可访问模式]一节解释了你如何在模式中使用隐参数。

::::setup
```
set_option linter.unusedVariables false
--------
def tail : List α → List α
  | []      => []
  | a :: as => as
```

:::leanFirst
-- As described in {ref "inductive-types"}[Inductive Types],
-- inductive data types can depend on parameters. The following example defines
-- the {name}`tail` function using pattern matching. The argument {leanRef}`α : Type u`
-- is a parameter and occurs before the colon to indicate it does not participate in the pattern matching.
-- Lean also allows parameters to occur after the {leanRef}`:`, but pattern matching on them requires an explicit {leanRef}`match`.

正如{ref "inductive-types"}[归纳类型]一章中所描述的，归纳数据类型可以依赖于参数。下面的例子使用模式匹配定义了 {name}`tail` 函数。参数 {leanRef}`α : Type u` 是一个参数，出现在冒号之前，表示它不参与模式匹配。Lean 也允许参数出现在 {leanRef}`:` 之后，但需要显式的 {leanRef}`match` 才能模式匹配。

```lean
set_option linter.unusedVariables false
--------
def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as

def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as
```
:::
::::

-- Despite the different placement of the parameter {leanRef}`α` in these two
-- examples, in both cases it is treated in the same way, in that it does
-- not participate in a case split.

尽管参数 {leanRef}`α` 在这两个例子中的位置不同，但在这两种情况下，它的处理方式是一样的，即它不参与情况分割。

-- Lean can also handle more complex forms of pattern matching, in which
-- arguments to dependent types pose additional constraints on the
-- various cases. Such examples of _dependent pattern matching_ are
-- considered in the section on {ref "dependent-pattern-matching"}[dependent pattern matching].

Lean 也可以处理更复杂的模式匹配形式，其中从属类型的参数对各种情况构成了额外的约束。
这种 _依值模式匹配_ 的例子在 {ref "dependent-pattern-matching"}[依值模式匹配]一节中考虑。

-- # Wildcards and Overlapping Patterns
# 通配符和重叠模式
%%%
tag := "wildcards-and-overlapping-patterns"
%%%

-- Consider one of the examples from the last section:

考虑上节的一个例子：

```lean
set_option linter.unusedVariables false
--------
def foo : Nat → Nat → Nat
  | 0,     n     => 0
  | m + 1, 0     => 1
  | m + 1, n + 1 => 2
```

-- An alternative presentation is:

也可以表述成：

```lean
set_option linter.unusedVariables false
--------
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
```

-- In the second presentation, the patterns overlap; for example, the
-- pair of arguments {lit}`0, 0` matches all three cases. But Lean handles
-- the ambiguity by using the first applicable equation, so in this example
-- the net result is the same. In particular, the following equations hold
-- definitionally:

在第二种表述中，模式是重叠的；例如，一对参数 {lit}`0, 0` 符合所有三种情况。但是 Lean 通过使用第一个适用的方程来处理这种模糊性，
所以在这个例子中，最终结果是一样的。特别是，以下方程在定义上是成立的：

```lean
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
------
example : foo 0       0       = 0 := rfl
example : foo 0       (n + 1) = 0 := rfl
example : foo (m + 1) 0       = 1 := rfl
example : foo (m + 1) (n + 1) = 2 := rfl
```

-- Since the values of {leanRef (in:="m, n")}`m` and {leanRef (in:="m, n")}`n` are not needed, we can just as well use wildcard patterns instead.

由于不需要 {leanRef (in:="m, n")}`m` 和 {leanRef (in:="m, n")}`n` 的值，我们也可以用通配符模式代替。

```lean
def foo : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2
```

-- You can check that this definition of {leanRef}`foo` satisfies the same
-- definitional identities as before.

你可以检查这个 {leanRef}`foo` 的定义是否满足与之前相同的定义特性。

:::setup
```
variable (α : Type u) (a : α)
```

-- Some functional programming languages support _incomplete
-- patterns_. In these languages, the interpreter produces an exception
-- or returns an arbitrary value for incomplete cases. We can simulate
-- the arbitrary value approach using the {lean}`Inhabited` type
-- class. Roughly, an element of {lean}`Inhabited α` is a witness to the fact
-- that there is an element of {lean}`α`; in {ref "type-classes"}[the chapter on type classes]
-- we will see that Lean can be instructed that suitable
-- base types are inhabited, and can automatically infer that other
-- constructed types are inhabited. On this basis, the
-- standard library provides a default element, {lean}`default`, of
-- any inhabited type.

-- We can also use the type {lean}`Option α` to simulate incomplete patterns.
-- The idea is to return {lean}`some a` for the provided patterns, and use
-- {lean (type:="Option α")}`none` for the incomplete cases. The following example demonstrates
-- both approaches.

一些函数式编程语言支持 _不完整的模式_ 。在这些语言中，解释器对不完整的情况产生一个异常或返回一个任意的值。
我们可以使用 {lean}`Inhabited` （含元素的）类型类来模拟任意值的方法。粗略的说，{lean}`Inhabited α` 的一个元素是对 {lean}`α` 拥有一个元素的见证；
在 {ref "type-classes"}[类型类]一章中，我们将看到 Lean 可以被告知合适的基础类型是含元素的，并且可以自动推断出其他构造类型是含元素的。
在此基础上，标准库提供了一个任意元素 {lean}`default`，任何含元素的类型。

我们还可以使用类型 {lean}`Option α` 来模拟不完整的模式。我们的想法是对所提供的模式返回 {lean}`some a`，
而对不完整的情况使用 {lean (type:="Option α")}`none`。下面的例子演示了这两种方法。
:::

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

-- The equation compiler is clever. If you leave out any of the cases in
-- the following definition, the error message will let you know what has
-- not been covered.

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

-- It will also use an {kw}`if`{lit}`  ...  `{kw}`then`{lit}`  ...  `{kw}`else` instead of a {lit}`casesOn` in appropriate situations.

某些情况也可以用 {kw}`if`{lit}`  ...  `{kw}`then`{lit}`  ...  `{kw}`else` 代替 {lit}`casesOn`。

```lean
set_option pp.proofs true
-------
def foo : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
```

-- # Structural Recursion and Induction
# 结构化递归和归纳
%%%
tag := "structural-recursion-and-induction"
%%%

-- What makes the equation compiler powerful is that it also supports
-- recursive definitions. In the next three sections, we will describe,
-- respectively:

-- - structurally recursive definitions
-- - well-founded recursive definitions
-- - mutually recursive definitions

-- Generally speaking, the equation compiler processes input of the following form:

方程编译器的强大之处在于，它还支持递归定义。在接下来的三节中，我们将分别介绍。

- 结构性递归定义
- 良基的递归定义
- 相互递归的定义

一般来说，方程编译器处理以下形式的输入：

```
def foo (a : α) : (b : β) → γ
  | [patterns₁] => t₁
  ...
  | [patternsₙ] => tₙ
```

-- Here {lit}`(a : α)` is a sequence of parameters, {lit}`(b : β)` is the
-- sequence of arguments on which pattern matching takes place, and {lit}`γ`
-- is any type, which can depend on {lit}`a` and {lit}`b`. Each line should
-- contain the same number of patterns, one for each element of {lit}`β`. As we
-- have seen, a pattern is either a variable, a constructor applied to
-- other patterns, or an expression that normalizes to something of that
-- form (where the non-constructors are marked with the {attr}`[match_pattern]`
-- attribute). The appearances of constructors prompt case splits, with
-- the arguments to the constructors represented by the given
-- variables. In the section on {ref "dependent-pattern-matching"}[dependent pattern matching],
-- we will see that some explicit terms in patterns are forced into a particular form
-- in order to make an expression type check, though they do not play a
-- role in pattern matching. These are called “{deftech}[inaccessible patterns]” for
-- that reason. But we will not need to use such inaccessible patterns
-- before covering {ref "dependent-pattern-matching"}[dependent pattern matching].

这里 {lit}`(a : α)` 是一个参数序列，{lit}`(b : β)` 是进行模式匹配的参数序列，{lit}`γ` 是任何类型，
它可以取决于 {lit}`a` 和 {lit}`b`。每一行应该包含相同数量的模式，对应于 {lit}`β` 的每个元素。
正如我们所看到的，模式要么是一个变量，要么是应用于其他模式的构造子，要么是一个正规化为该形式的表达式
（其中非构造子用 {attr}`[match_pattern]` 属性标记）。构造子的出现会提示情况拆分，构造子的参数由给定的变量表示。
在 {ref "dependent-pattern-matching"}[依值模式匹配]一节中，我们将看到有时有必要在模式中包含明确的项，
这些项需要进行表达式类型检查，尽管它们在模式匹配中没有起到作用。由于这个原因，这些被称为“{deftech}[不可访问的模式]”。
但是在 {ref "dependent-pattern-matching"}[依值模式匹配]一节之前，我们将不需要使用这种不可访问的模式。

-- As we saw in the last section, the terms {lit}`t₁, ..., tₙ` can make use
-- of any of the parameters {lit}`a`, as well as any of the variables that
-- are introduced in the corresponding patterns. What makes recursion and
-- induction possible is that they can also involve recursive calls to
-- {lit}`foo`. In this section, we will deal with _structural recursion_, in
-- which the arguments to {lit}`foo` occurring on the right-hand side of the
-- {lit}`=>` are subterms of the patterns on the left-hand side. The idea is
-- that they are structurally smaller, and hence appear in the inductive
-- type at an earlier stage. Here are some examples of structural
-- recursion from the last chapter, now defined using the equation
-- compiler:

正如我们在上一节所看到的，项 {lit}`t₁, ..., tₙ` 可以利用任何一个参数 {lit}`a`，以及在相应模式中引入的任何一个变量。
使得递归和归纳成为可能的是，它们也可以涉及对 {lit}`foo` 的递归调用。在本节中，我们将处理 _结构性递归_ ，
其中 {lit}`foo` 的参数出现在 {lit}`=>` 的右侧，是左侧模式的子项。我们的想法是，它们在结构上更小，
因此在归纳类型中出现在更早的阶段。下面是上一章的一些结构递归的例子，现在用方程编译器来定义：

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

-- The proof of {leanRef}`zero_add` makes it clear that proof by induction is
-- really a form of recursion in Lean.

{leanRef}`zero_add` 的证明清楚地表明，归纳证明实际上是 Lean 中的一种递归形式。

-- The example above shows that the defining equations for {leanRef}`add` hold
-- definitionally, and the same is true of {leanRef}`mul`. The equation compiler
-- tries to ensure that this holds whenever possible, as is the case with
-- straightforward structural induction. In other situations, however,
-- reductions hold only _propositionally_, which is to say, they are
-- equational theorems that must be applied explicitly. The equation
-- compiler generates such theorems internally. They are not meant to be
-- used directly by the user; rather, the {tactic}`simp` tactic
-- is configured to use them when necessary. The following
-- proof of {leanRef}`zero_add` works this way:

上面的例子表明，{leanRef}`add` 的定义方程具有定义意义，{leanRef}`mul` 也是如此。方程编译器试图确保在任何可能的情况下都是这样，
就像直接的结构归纳法一样。然而，在其他情况下，约简只在 _命题_ 上成立，也就是说，它们是必须明确应用的方程定理。
方程编译器在内部生成这样的定理。用户不能直接使用它们；相反，{tactic}`simp` 策略被配置为在必要时使用它们。
因此，对 {leanRef}`zero_add` 的以下两种证明都成立：

```lean
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)
-----
theorem zero_add : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]
```

-- As with definition by pattern matching, parameters to a structural
-- recursion or induction may appear before the colon. Such parameters
-- are simply added to the local context before the definition is
-- processed. For example, the definition of addition may also be written
-- as follows:

与模式匹配定义一样，结构递归或归纳的参数可能出现在冒号之前。在处理定义之前，简单地将这些参数添加到本地上下文中。
例如，加法的定义也可以写成这样：

```lean
open Nat
def add (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)
```

-- You can also write the example above using {kw}`match`.

你也可以用 {kw}`match` 来写上面的例子。

```lean
open Nat
def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)
```

:::leanFirst
-- A more interesting example of structural recursion is given by the Fibonacci function {leanRef}`fib`.

一个更有趣的结构递归的例子是斐波那契函数 {leanRef}`fib`。

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
:::
:::setup
```
variable (n : Nat)
open Nat
```

-- Here, the value of the {leanRef}`fib` function at {leanRef}`n + 2` (which is
-- definitionally equal to {lean}`succ (succ n)`) is defined in terms of the
-- values at {leanRef}`n + 1` (which is definitionally equivalent to {lean}`succ n`)
-- and the value at {leanRef}`n`. This is a notoriously inefficient way of
-- computing the Fibonacci function, however, with an execution time that
-- is exponential in {lean}`n`. Here is a better way:

这里，{leanRef}`fib` 函数在 {leanRef}`n + 2` （定义上等于 {lean}`succ (succ n)` ）处的值是根据 {leanRef}`n + 1`
（定义上等价于 {lean}`succ n` ）和 {leanRef}`n` 处的值定义的。然而，这是一种众所周知的计算斐波那契函数的低效方法，
其执行时间是 {lean}`n` 的指数级。这里有一个更好的方法：
:::
```



```lean
def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100 -- 573147844013817084101
```

-- Here is the same definition using a {kw}`let rec` instead of a {kw}`where`.

这里是使用 {kw}`let rec` 而不是 {kw}`where` 的相同定义。

```lean
def fibFast (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2
```

-- In both cases, Lean generates the auxiliary function {lit}`fibFast.loop`.

在这两种情况下，Lean 都会生成辅助函数 {lit}`fibFast.loop`。

:::leanFirst
-- To handle structural recursion, the equation compiler uses
-- _course-of-values_ recursion, using constants {lit}`below` and {lit}`brecOn`
-- that are automatically generated with each inductively defined
-- type. You can get a sense of how it works by looking at the types of
-- {leanRef}`Nat.below` and {leanRef}`Nat.brecOn`:

为了处理结构递归，方程编译器使用 _值域_ 递归（course-of-values recursion），使用每个归纳定义类型自动生成的常量 {lit}`below` 和 {lit}`brecOn`。
你可以通过查看 {leanRef}`Nat.below` 和 {leanRef}`Nat.brecOn` 的类型来了解它是如何工作的：

```lean
variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
```
:::
:::setup
```
variable (C : Nat → Type u) (n : Nat)
```
-- The type {lean}`@Nat.below C (3 : Nat)` is a data structure that stores elements of {lean}`C 0`, {lean}`C 1`, and {lean}`C 2`.
-- The course-of-values recursion is implemented by {name}`Nat.brecOn`. It enables us to define the value of a dependent
-- function of type {lean}`(n : Nat) → C n` at a particular input {lean}`n` in terms of all the previous values of the function,
-- presented as an element of {lean}`@Nat.below C n`.

类型 {lean}`@Nat.below C (3 : Nat)` 是一个数据结构，它存储 {lean}`C 0`、{lean}`C 1` 和 {lean}`C 2` 的元素。
值域递归由 {name}`Nat.brecOn` 实现。它使我们能够根据函数的所有先前值（表示为 {lean}`@Nat.below C n` 的元素）
定义类型为 {lean}`(n : Nat) → C n` 的依赖函数在特定输入 {lean}`n` 处的值。
:::

:::leanFirst
-- The use of course-of-values recursion is one of the techniques the equation compiler uses to justify to
-- the Lean kernel that a function terminates. It does not affect the code generator which compiles recursive
-- functions as other functional programming language compilers. Recall that {kw}`#eval`{lit}` ` {leanRef}`fib`{lit}` <n>` is exponential in {lit}`<n>`.
-- On the other hand, {kw}`#reduce`{lit}` `{leanRef}`fib`{lit}` <n>` is efficient because it uses the definition sent to the kernel that
-- is based on the {lit}`brecOn` construction.

使用值域递归是方程编译器用来向 Lean 内核证明函数终止的技术之一。它不影响代码生成器，代码生成器像其他函数式编程语言编译器一样编译递归函数。
回想一下，{kw}`#eval`{lit}` ` {leanRef}`fib`{lit}` <n>` 在 {lit}`<n>` 上是指数级的。
另一方面，{kw}`#reduce`{lit}` `{leanRef}`fib`{lit}` <n>` 是高效的，因为它使用发送到内核的基于 {lit}`brecOn` 构造的定义。

```lean
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

-- Slow:
-- #eval fib 50
-- Fast:
#reduce fib 50

#print fib
```
:::

:::leanFirst
-- Another good example of a recursive definition is the list {leanRef}`append` function.

递归定义的另一个很好的例子是列表 {leanRef}`append` 函数。

```lean
def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl
```
:::

-- Here is another: it adds elements of the first list to elements of the second list, until one of the two lists runs out.

这里还有另一个例子：它将第一个列表的元素添加到第二个列表的元素中，直到两个列表中的一个用完为止。

```lean
def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10] -- [5, 7, 9]
```

-- You are encouraged to experiment with similar examples in the exercises below.

鼓励你在下面的练习中尝试类似的例子。

-- # Local recursive declarations
# 局部递归声明
%%%
tag := "local-recursive-declarations"
%%%

-- You can define local recursive declarations using the {kw}`let rec` keyword.

你可以使用 {kw}`let rec` 关键字定义局部递归声明。

```lean
def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop -- @replicate.loop : {α : Type u_1} → α → Nat → List α → List α
```

-- Lean creates an auxiliary declaration for each {leanRef}`let rec`. In the example above,
-- it created the declaration {leanRef}`replicate.loop` for the {leanRef}`let rec loop` occurring at {leanRef}`replicate`.
-- Note that, Lean “closes” the declaration by adding any local variable occurring in the
-- {leanRef}`let rec` declaration as additional parameters. For example, the local variable {leanRef}`a` occurs
-- at {leanRef}`let rec loop`.

Lean 为每个 {leanRef}`let rec` 创建一个辅助声明。在上面的例子中，它为出现在 {leanRef}`replicate` 中的 {leanRef}`let rec loop` 创建了声明 {leanRef}`replicate.loop`。
注意，Lean 通过将出现在 {leanRef}`let rec` 声明中的任何局部变量添加为附加参数来“闭合”声明。例如，局部变量 {leanRef}`a` 出现在 {leanRef}`let rec loop` 中。


-- You can also use {leanRef}`let rec` in tactic mode and for creating proofs by induction.

你也可以在策略模式下使用 {leanRef}`let rec`，以及用于创建归纳证明。

```lean
def replicate (n : Nat) (a : α) : List α :=
 let rec loop : Nat → List α → List α
   | 0,   as => as
   | n+1, as => loop n (a::as)
 loop n []
------
theorem length_replicate (n : Nat) (a : α) :
    (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α) :
      (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp +arith [replicate.loop, aux n]
  exact aux n []
```

-- You can also introduce auxiliary recursive declarations using {kw}`where` clause after your definition.
-- Lean converts them into a {kw}`let rec`.

你也可以在定义之后使用 {kw}`where` 子句引入辅助递归声明。
Lean 将它们转换为 {kw}`let rec`。

```lean
def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) :
    (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α) :
      (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp +arith [replicate.loop, aux n]
```

-- # Well-Founded Recursion and Induction
# 良基递归和归纳
%%%
tag := "well-founded-recursion-and-induction"
%%%

-- When structural recursion cannot be used, we can prove termination using well-founded recursion.
-- We need a well-founded relation and a proof that each recursive application is decreasing with respect to
-- this relation. Dependent type theory is powerful enough to encode and justify
-- well-founded recursion. Let us start with the logical background that
-- is needed to understand how it works.

当无法使用结构递归时，我们可以使用良基递归来证明终止。
我们需要一个良基关系，以及一个证明，证明每个递归应用相对于该关系都是递减的。
依赖类型理论足够强大，可以编码和证明良基递归。让我们从理解其工作原理所需的逻辑背景开始。

:::setup
```
variable (α : Type u) (a : α) (r : α → α → Prop)
```

-- Lean's standard library defines two predicates, {lean}`Acc r a` and
-- {lean}`WellFounded r`, where {lean}`r` is a binary relation on a type {lean}`α`,
-- and {lean}`a` is an element of type {lean}`α`.

Lean 的标准库定义了两个谓词 {lean}`Acc r a` 和 {lean}`WellFounded r`，其中 {lean}`r` 是类型 {lean}`α` 上的二元关系，
{lean}`a` 是类型 {lean}`α` 的元素。
:::

```lean
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)
```

```lean (show := false)
variable {α : Sort u} (x y : α)
variable {r : α → α → Prop}

example : Acc r x = ∀ y, r y x → Acc r y := by
  simp only [eq_iff_iff]
  constructor
  . intro ⟨_, hAcc⟩
    assumption
  . intro h
    constructor
    assumption

def r' : α → α → Prop := fun x y => True
infix:50 " ≺ " => r'
example : y ≺ x := True.intro
example := WellFounded r
```


-- The first, {leanRef}`Acc`, is an inductively defined predicate. According to
-- its definition, {leanRef}`Acc r x` is equivalent to
-- {leanRef}`∀ y, r y x → Acc r y`. If you think of {leanRef}`r y x` as denoting a kind of order relation
-- {leanRef}`y ≺ x`, then {leanRef}`Acc r x` says that {leanRef}`x` is accessible from below,
-- in the sense that all its predecessors are accessible. In particular,
-- if {leanRef}`x` has no predecessors, it is accessible. Given any type {leanRef}`α`,
-- we should be able to assign a value to each accessible element of
-- {leanRef}`α`, recursively, by assigning values to all its predecessors first.

第一个 {leanRef}`Acc` 是一个归纳定义的谓词。根据其定义，{leanRef}`Acc r x` 等价于 {leanRef}`∀ y, r y x → Acc r y`。
如果你认为 {leanRef}`r y x` 表示一种顺序关系 {leanRef}`y ≺ x`，那么 {leanRef}`Acc r x` 表示 {leanRef}`x` 是从下方可访问的，
即它的所有前驱都是可访问的。特别是，如果 {leanRef}`x` 没有前驱，它是可访问的。给定任何类型 {leanRef}`α`，
我们应该能够递归地为 {leanRef}`α` 的每个可访问元素赋值，方法是首先为其所有前驱赋值。



-- The statement that {leanRef}`r` is well-founded, denoted {leanRef}`WellFounded r`,
-- is exactly the statement that every element of the type is
-- accessible. By the above considerations, if {leanRef}`r` is a well-founded
-- relation on a type {leanRef}`α`, we should have a principle of well-founded
-- recursion on {leanRef}`α`, with respect to the relation {leanRef}`r`. And, indeed,
-- we do: the standard library defines {name}`WellFounded.fix`, which serves
-- exactly that purpose.

关于 {leanRef}`r` 是良基的陈述，记为 {leanRef}`WellFounded r`，正是该类型的每个元素都是可访问的陈述。
根据上述考虑，如果 {leanRef}`r` 是类型 {leanRef}`α` 上的良基关系，我们应该在 {leanRef}`α` 上有一个关于关系 {leanRef}`r` 的良基递归原理。
确实，我们有：标准库定义了 {name}`WellFounded.fix`，它正是用于此目的。

```lean
noncomputable
def f {α : Sort u}
    (r : α → α → Prop)
    (h : WellFounded r)
    (C : α → Sort v)
    (F : (x : α) → ((y : α) → r y x → C y) → C x) :
    (x : α) → C x :=
WellFounded.fix h F
```

-- There is a long cast of characters here, but the first block we have
-- already seen: the type, {leanRef}`α`, the relation, {leanRef}`r`, and the
-- assumption, {leanRef}`h`, that {leanRef}`r` is well-founded. The variable {leanRef}`C`
-- represents the motive of the recursive definition: for each element
-- {leanRef}`x : α`, we would like to construct an element of {leanRef}`C x`. The
-- function {leanRef}`F` provides the inductive recipe for doing that: it tells
-- us how to construct an element {leanRef}`C x`, given elements of {leanRef}`C y` for
-- each predecessor {leanRef}`y` of {leanRef}`x`.

这里有很多角色，但我们已经看到了第一块：类型 {leanRef}`α`，关系 {leanRef}`r`，以及假设 {leanRef}`h`，即 {leanRef}`r` 是良基的。
变量 {leanRef}`C` 代表递归定义的动机：对于每个元素 {leanRef}`x : α`，我们想要构造一个 {leanRef}`C x` 的元素。
函数 {leanRef}`F` 提供了这样做的归纳配方：它告诉我们如何构造一个元素 {leanRef}`C x`，给定 {leanRef}`x` 的每个前驱 {leanRef}`y` 的 {leanRef}`C y` 元素。

:::setup
```
variable {x y : α} (C : α → Sort v) (r : α → α → Prop)

```

-- Note that {name}`WellFounded.fix` works equally well as an induction
-- principle. It says that if {leanRef}`≺` is well-founded and you want to prove
-- {lean}`∀ x, C x`, it suffices to show that for an arbitrary {lean}`x`, if we
-- have {lean}`∀ y, r y x → C y`, then we have {lean}`C x`.

注意，{name}`WellFounded.fix` 同样可以作为归纳原理。它说如果 {leanRef}`≺` 是良基的，并且你想证明 {lean}`∀ x, C x`，
只要证明对于任意 {lean}`x`，如果我们有 {lean}`∀ y, r y x → C y`，那么我们有 {lean}`C x` 就足够了。
:::

-- In the example above we use the modifier {leanRef}`noncomputable` because the code
-- generator currently does not support {name}`WellFounded.fix`. The function
-- {name}`WellFounded.fix` is another tool Lean uses to justify that a function
-- terminates.

在上面的例子中，我们使用修饰符 {leanRef}`noncomputable`，因为代码生成器目前不支持 {name}`WellFounded.fix`。
函数 {name}`WellFounded.fix` 是 Lean 用来证明函数终止的另一个工具。

-- Lean knows that the usual order {lit}`<` on the natural numbers is well
-- founded. It also knows a number of ways of constructing new well
-- founded orders from others, for example, using lexicographic order.

Lean 知道自然数上的通常顺序 {lit}`<` 是良基的。它还知道许多从其他良基顺序构造新良基顺序的方法，例如使用字典序。

-- Here is essentially the definition of division on the natural numbers that is found in the standard library.

这本质上是标准库中自然数除法的定义。

```lean
------
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

:::TODO
Missing HL for example
-- The definition is somewhat inscrutable. Here the recursion is on
-- {leanRef (in:="def div.F (x")}`x`, and {lit}`div.F x f : Nat → Nat` returns the “divide by {leanRef}`y`”
-- function for that fixed {leanRef (in:="def div.F (x")}`x`. You have to remember that the second
-- argument to {leanRef}`div.F`, the recipe for the recursion, is a function
-- that is supposed to return the divide by {leanRef}`y` function for all values
-- {leanRef}`x₁` smaller than {leanRef}`x`.

这个定义有点难以理解。这里的递归是在 {leanRef (in:="def div.F (x")}`x` 上进行的，{lit}`div.F x f : Nat → Nat` 返回该固定 {leanRef (in:="def div.F (x")}`x` 的“除以 {leanRef}`y`”函数。
你必须记住，{leanRef}`div.F` 的第二个参数（递归的配方）是一个函数，它应该返回所有小于 {leanRef}`x` 的值 {leanRef}`x₁` 的除以 {leanRef}`y` 函数。
:::

-- The elaborator is designed to make definitions like this more
-- convenient. It accepts the following:

繁饰器（Elaborator）可以使这样的定义更加方便。它接受下列内容：

```lean
def div (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div (x - y) y + 1
  else
    0
```

-- When Lean encounters a recursive definition, it first
-- tries structural recursion, and only when that fails, does it fall
-- back on well-founded recursion. Lean uses the tactic {tactic}`decreasing_tactic`
-- to show that the recursive applications are smaller. The auxiliary
-- proposition {leanRef}`x - y < x` in the example above should be viewed as a hint
-- for this tactic.

当 Lean 遇到递归定义时，它首先尝试结构递归，失败时才返回到良基递归。Lean 使用 {tactic}`decreasing_tactic` 来显示递归应用会越来越小。
上面例子中的辅助命题 {leanRef}`x - y < x` 应该被视为这种策略的提示。

-- The defining equation for {leanRef}`div` does _not_ hold definitionally, but
-- we can unfold {leanRef}`div` using the {tactic}`unfold` tactic. We use {ref "conv"}[{tactic}`conv`] to select which
-- {leanRef}`div` application we want to unfold.

{leanRef}`div` 的定义公式不具有定义性，但我们可以使用 {tactic}`unfold` 策略展开 {leanRef}`div`。
我们使用 {ref "conv"}[{tactic}`conv`] 来选择要展开的 {leanRef}`div` 应用。

```lean
def div (x y : Nat) : Nat :=
 if h : 0 < y ∧ y ≤ x then
   have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
   div (x - y) y + 1
 else
   0
------
example (x y : Nat) :
    div x y =
    if 0 < y ∧ y ≤ x then
      div (x - y) y + 1
    else 0 := by
   -- unfold occurrence in the left-hand-side of the equation:
  conv => lhs; unfold div
  rfl

example (x y : Nat) (h : 0 < y ∧ y ≤ x) :
    div x y = div (x - y) y + 1 := by
  conv => lhs; unfold div
  simp [h]
```

:::leanFirst
-- The following example is similar: it converts any natural number to a
-- binary expression, represented as a list of 0's and 1's. We have to
-- provide evidence that the recursive call is
-- decreasing, which we do here with a {leanRef}`sorry`. The {leanRef}`sorry` does not
-- prevent the interpreter from evaluating the function successfully,
-- but {leanRef}`#eval!` must be used instead of {kw}`#eval` when a term contains {leanRef}`sorry`.

下面的示例与此类似：它将任何自然数转换为二进制表达式，表示为 0 和 1 的列表。我们必须提供递归调用正在递减的证据，
我们在这里用 {leanRef}`sorry` 来做。{leanRef}`sorry` 并不会阻止解释器成功地对函数求值，
但是当一个项包含 {leanRef}`sorry` 时，必须使用 {leanRef}`#eval!` 而不是 {kw}`#eval`。

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2]

#eval! natToBin 1234567
```
:::

:::leanFirst
-- As a final example, we observe that Ackermann's function can be
-- defined directly, because it is justified by the well-foundedness of
-- the lexicographic order on the natural numbers. The {leanRef}`termination_by` clause
-- instructs Lean to use a lexicographic order. This clause is actually mapping
-- the function arguments to elements of type {lean}`Nat × Nat`. Then, Lean uses typeclass
-- resolution to synthesize an element of type {lean}`WellFoundedRelation (Nat × Nat)`.

最后一个例子，我们观察到 Ackermann 函数可以直接定义，因为它可以被自然数上字典序的良基性证明。
{leanRef}`termination_by` 子句指示 Lean 使用字典序。这个子句实际上是将函数参数映射到类型为 {lean}`Nat × Nat` 的元素。
然后，Lean 使用类型类解析来合成类型为 {lean}`WellFoundedRelation (Nat × Nat)` 的元素。

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
```
:::

-- In many cases, Lean can automatically determine an appropriate lexicographical order.
-- Ackermann's function is one such case, so the {leanRef}`termination_by` clause is optional:

在许多情况下，Lean 可以自动确定适当的字典序。Ackermann 函数就是这样一种情况，因此 {leanRef}`termination_by` 子句是可选的：

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
```

:::setup
```
variable {α : Type u} {β : Type v}
```

-- Note that a lexicographic order is used in the example above because the instance
-- {lean}`WellFoundedRelation (α × β)` uses a lexicographic order. Lean also defines the instance

注意，在上面的例子中使用了字典序，因为实例 {lean}`WellFoundedRelation (α × β)` 使用了字典序。Lean 还定义了实例

```lean
instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel
```
:::

:::leanFirst
-- In the following example, we prove termination by showing that {leanRef}`as.size - i` is decreasing
-- in the recursive application.

在下面的例子中，我们通过显示 {leanRef}`as.size - i` 在递归应用中是递减的来证明它会终止。

```lean
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as[i]
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
  termination_by as.size - i
```
:::
-- Note that, auxiliary function {leanRef}`go` is recursive in this example, but {leanRef}`takeWhile` is not.
-- Once again, Lean can automatically recognize this pattern, so the {leanRef}`termination_by` clause is unnecessary:

注意，辅助函数 {leanRef}`go` 在这个例子中是递归的，但 {leanRef}`takeWhile` 不是。
Lean 再次可以自动识别这种模式，因此 {leanRef}`termination_by` 子句是不必要的：
```lean
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as[i]
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
```

:::leanFirst
-- By default, Lean uses the tactic {tactic}`decreasing_tactic` to prove recursive applications are decreasing. The modifier {leanRef}`decreasing_by` allows us to provide our own tactic. Here is an example.

默认情况下，Lean 使用 {tactic}`decreasing_tactic` 来证明递归应用正在递减。修饰词 {leanRef}`decreasing_by` 允许我们提供自己的策略。这里有一个例子。

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
:::

-- Note that {leanRef}`decreasing_by` is not replacement for {leanRef}`termination_by`, they complement each other. {leanRef}`termination_by` is used to specify a well-founded relation, and {leanRef}`decreasing_by` for providing our own tactic for showing recursive applications are decreasing. In the following example, we use both of them.

注意 {leanRef}`decreasing_by` 不是 {leanRef}`termination_by` 的替代品，它们是互补的。{leanRef}`termination_by` 用于指定良基关系，
而 {leanRef}`decreasing_by` 用于提供我们自己的策略来显示递归应用正在递减。在下面的例子中，我们同时使用了它们。

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
decreasing_by
   -- unfolds well-founded recursion auxiliary definitions:
  all_goals simp_wf
  · apply Prod.Lex.left; simp +arith
  · apply Prod.Lex.right; simp +arith
  · apply Prod.Lex.left; simp +arith
```

:::leanFirst
-- We can use {leanRef}`decreasing_by sorry` to instruct Lean to “trust” us that the function terminates.

我们可以使用 {leanRef}`decreasing_by sorry` 来指示 Lean “相信”我们函数会终止。

```lean
def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 => natToBin ((n + 2) / 2) ++ [n % 2]
decreasing_by sorry

#eval! natToBin 1234567
```
:::

:::leanFirst
-- Recall that using {leanRef}`sorry` is equivalent to using a new axiom, and should be avoided. In the following example, we used the {leanRef}`sorry` to prove {leanRef}`False`.
-- The command {leanRef}`#print axioms unsound` shows that {leanRef}`unsound` depends on the unsound axiom {lean}`sorryAx` used to implement {leanRef}`sorry`.

回想一下，使用 {leanRef}`sorry` 等同于使用一个新的公理，应该避免。在下面的例子中，我们使用 {leanRef}`sorry` 来证明 {leanRef}`False`。
命令 {leanRef}`#print axioms unsound` 显示 {leanRef}`unsound` 依赖于用于实现 {leanRef}`sorry` 的不安全公理 {lean}`sorryAx`。

```lean
def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
-- `unsound 0` is a proof of `False`

#print axioms unsound -- 'unsound' depends on axioms: [sorryAx]
```
:::

:::setup
```
variable {α : Type w} {β  : Type u} {γ : Type v} {G : Prop}
```

-- Summary:

-- - If there is no {leanRef}`termination_by`, a well-founded relation is derived (if possible) by selecting an argument and then using typeclass resolution to synthesize a well-founded relation for this argument's type.

-- - If {leanRef}`termination_by` is specified, it maps the arguments of the function to a type {lean}`α` and type class resolution is again used. Recall that, the default instance for {lean}`β × γ` is a lexicographic order based on the well-founded relations for {lean}`β` and {lean}`γ`.

-- - The default well-founded relation instance for {lean}`Nat` is {lean (type := "Nat → Nat → Prop")}`(· < ·)`.

-- - By default, the tactic {tactic}`decreasing_tactic` is used to show that recursive applications are smaller with respect to the selected well-founded relation. If {tactic}`decreasing_tactic` fails, the error message includes the remaining goal {lit}`... |- G`. Note that, the {tactic}`decreasing_tactic` uses {tactic}`assumption`. So, you can include a {kw}`have`-expression to prove goal {lean}`G`. You can also provide your own tactic using {kw}`decreasing_by`.

总结：

- 如果没有 {leanRef}`termination_by`，则通过选择一个参数，然后使用类型类解析为该参数的类型合成一个良基关系，从而推导出一个良基关系（如果可能的话）。

- 如果指定了 {leanRef}`termination_by`，它将函数的参数映射到类型 {lean}`α`，并再次使用类型类解析。回想一下，{lean}`β × γ` 的默认实例是基于 {lean}`β` 和 {lean}`γ` 的良基关系的字典序。

- {lean}`Nat` 的默认良基关系实例是 {lean (type := "Nat → Nat → Prop")}`(· < ·)`。

- 默认情况下，策略 {tactic}`decreasing_tactic` 用于显示递归应用相对于所选良基关系是更小的。如果 {tactic}`decreasing_tactic` 失败，错误消息将包含剩余的目标 {lit}`... |- G`。注意，{tactic}`decreasing_tactic` 使用 {tactic}`assumption`。因此，你可以包含一个 {kw}`have` 表达式来证明目标 {lean}`G`。你也可以使用 {kw}`decreasing_by` 提供你自己的策略。
:::

-- # Functional Induction
# 函数归纳
%%%
tag := "functional-induction"
%%%

-- Lean generates bespoke induction principles for recursive functions. These induction principles follow the recursive structure of the function's definition, rather than the structure of the datatype. Proofs about functions typically follow the recursive structure of the function itself, so these induction principles allow statements about the function to be proved more conveniently.

Lean 为递归函数生成定制的归纳原理。这些归纳原理遵循函数定义的递归结构，而不是数据类型的结构。
关于函数的证明通常遵循函数本身的递归结构，因此这些归纳原理允许更方便地证明关于函数的陈述。

:::leanFirst
-- For example, using the functional induction principle for {leanRef}`ack` to prove that the result is always greater than {leanRef}`0` requires one case for each arm of the pattern match in {leanRef}`ack`:

例如，使用 {leanRef}`ack` 的函数归纳原理来证明结果总是大于 {leanRef}`0`，需要为 {leanRef}`ack` 中的每个模式匹配分支提供一个案例：

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

theorem ack_gt_zero : ack n m > 0 := by
  fun_induction ack with
  | case1 y =>
--          ^ PROOF_STATE: case1
    simp
  | case2 x ih =>
--             ^ PROOF_STATE: case2
    exact ih
  | case3 x y ih1 ih2 =>
--                    ^ PROOF_STATE: case3
    simp [ack, *]
```
:::

-- In {goal case1}`case1`, the goal is:



在 {goal case1}`case1` 中，目标是：
```proofState case1
case case1
y : Nat
⊢ y + 1 > 0
```
-- The {leanRef}`y + 1` in the goal corresponds to the value returned in the first case of {leanRef}`ack`.
目标中的 {leanRef}`y + 1` 对应于 {leanRef}`ack` 第一种情况返回的值。

-- In {goal case2}`case2`, the goal is:


在 {goal case2}`case2` 中，目标是：
```proofState case2
case case2
x : Nat
ih : ack x 1 > 0
⊢ ack x 1 > 0
```

-- The {leanRef}`ack x 1` in the goal corresponds to the value of {leanRef}`ack` applied to the pattern variables {leanRef}`x + 1` and {leanRef}`0` returned in the second case of {leanRef}`ack`.
-- This term is automatically simplified to the right-hand side.
-- Happily, the inductive hypothesis {leanRef}`ih : ack x 1 > 0` corresponds to the recursive call, which is exactly the answer returned in this case.

目标中的 {leanRef}`ack x 1` 对应于 {leanRef}`ack` 应用于 {leanRef}`ack` 第二种情况返回的模式变量 {leanRef}`x + 1` 和 {leanRef}`0` 的值。
该项自动简化为右侧。令人高兴的是，归纳假设 {leanRef}`ih : ack x 1 > 0` 对应于递归调用，这正是这种情况下返回的答案。

-- In {goal case3}`case3`, the goal is:

在 {goal case3}`case3` 中，目标是：

```proofState case3
case case3
x : Nat
y : Nat
ih1 : ack (x + 1) y > 0
ih2 : ack x (ack (x + 1) y) > 0
⊢ ack x (ack (x + 1) y) > 0
```


-- The {leanRef}`ack x (ack (x + 1) y)` in the goal corresponds to the value returned in the third case of {leanRef}`ack`, when {leanRef}`ack` applied to {leanRef}`x + 1` and {leanRef}`y + 1` has been reduced.
-- The inductive hypotheses {leanRef}`ih1 : ack (x + 1) y > 0` and {leanRef}`ih2 : ack x (ack (x + 1) y) > 0` correspond to the recursive calls, with {leanRef}`ih1` matching the nested recursive call.
-- Once again, the induction hypothesis is suitable.

目标中的 {leanRef}`ack x (ack (x + 1) y)` 对应于 {leanRef}`ack` 第三种情况返回的值，当 {leanRef}`ack` 应用于 {leanRef}`x + 1` 和 {leanRef}`y + 1` 时已约简。
归纳假设 {leanRef}`ih1 : ack (x + 1) y > 0` 和 {leanRef}`ih2 : ack x (ack (x + 1) y) > 0` 对应于递归调用，其中 {leanRef}`ih1` 匹配嵌套递归调用。
再一次，归纳假设是合适的。

-- Using {leanRef}`fun_induction ack` results in goals and induction hypotheses that match the recursive structure of {leanRef}`ack`. As a result, the proof can be a single line:

使用 {leanRef}`fun_induction ack` 会产生与 {leanRef}`ack` 的递归结构相匹配的目标和归纳假设。结果，证明可以只有一行：

```lean
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
-------------
theorem ack_gt_zero : ack n m > 0 := by
  fun_induction ack <;> simp [*, ack]
```

:::leanFirst
-- There is also a {leanRef}`fun_cases` tactic which is analogous to the {tactic}`cases` tactic.
-- It generates a case for each branch in a function's control flow.
-- Both it and {leanRef}`fun_induction` additionally provide assumptions that rule out the paths that were not taken.

还有一个 {leanRef}`fun_cases` 策略，类似于 {tactic}`cases` 策略。它为函数控制流中的每个分支生成一个案例。
它和 {leanRef}`fun_induction` 都额外提供了排除未采用路径的假设。

-- This function {leanRef}`f` represents a five-way Boolean disjunction:

这个函数 {leanRef}`f` 表示一个五路布尔析取：

```lean
def f : Bool → Bool → Bool → Bool → Bool → Bool
  | true, _, _, _ , _ => true
  | _, true, _, _ , _ => true
  | _, _, true, _ , _ => true
  | _, _, _, true, _  => true
  | _, _, _, _, x  => x

```

-- To prove that it is disjunction, the last case requires knowledge that none of the arguments are {leanRef}`true`.
-- This knowledge is provided by the tactic:

为了证明它是析取，最后一种情况需要知道没有任何参数是 {leanRef}`true`。这个知识由策略提供：

```lean
def f : Bool → Bool → Bool → Bool → Bool → Bool
  | true, _, _, _ , _ => true
  | _, true, _, _ , _ => true
  | _, _, true, _ , _ => true
  | _, _, _, true, _  => true
  | _, _, _, _, x  => x
------
theorem f_or : f b1 b2 b3 b4 b5 = (b1 || b2 || b3 || b4 || b5) := by
  fun_cases f
-- ^ PROOF_STATE: fOrAll
  all_goals sorry
```
:::

-- Each case includes an assumption that rules out the prior cases:

每个案例都包含一个排除先前案例的假设：

```proofState fOrAll
case case1
b2 : Bool
b3 : Bool
b4 : Bool
b5 : Bool
⊢ true = (true || b2 || b3 || b4 || b5)

case case2
b1 : Bool
b3 : Bool
b4 : Bool
b5 : Bool
x✝ : b1 = true → False
⊢ true = (b1 || true || b3 || b4 || b5)

case case3
b1 : Bool
b2 : Bool
b4 : Bool
b5 : Bool
x✝¹ : b1 = true → False
x✝ : b2 = true → False
⊢ true = (b1 || b2 || true || b4 || b5)

case case4
b1 : Bool
b2 : Bool
b3 : Bool
b5 : Bool
x✝² : b1 = true → False
x✝¹ : b2 = true → False
x✝ : b3 = true → False
⊢ true = (b1 || b2 || b3 || true || b5)

case case5
b1 : Bool
b2 : Bool
b3 : Bool
b4 : Bool
b5 : Bool
x✝³ : b1 = true → False
x✝² : b2 = true → False
x✝¹ : b3 = true → False
x✝ : b4 = true → False
⊢ b5 = (b1 || b2 || b3 || b4 || b5)
```

:::leanFirst
-- The {leanRef}`simp_all` tactic, which simplifies all the assumptions and the goal together, can dispatch all cases:

{leanRef}`simp_all` 策略将所有假设和目标一起简化，可以处理所有案例：

```lean
def f : Bool → Bool → Bool → Bool → Bool → Bool
  | true, _, _, _ , _ => true
  | _, true, _, _ , _ => true
  | _, _, true, _ , _ => true
  | _, _, _, true, _  => true
  | _, _, _, _, x  => x
------
theorem f_or : f b1 b2 b3 b4 b5 = (b1 || b2 || b3 || b4 || b5) := by
  fun_cases f <;> simp_all
```
:::


-- # Mutual Recursion
# 相互递归
%%%
tag := "mutual-recursion"
%%%

-- Lean also supports mutual recursive definitions. The syntax is similar to that for mutual inductive types. Here is an example:

Lean 也支持相互递归定义。语法类似于相互归纳类型。这里有一个例子：

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

-- What makes this a mutual definition is that {leanRef}`even` is defined recursively in terms of {leanRef}`odd`, while {leanRef}`odd` is defined recursively in terms of {leanRef}`even`. Under the hood, this is compiled as a single recursive definition. The internally defined function takes, as argument, an element of a sum type, either an input to {leanRef}`even`, or an input to {leanRef}`odd`. It then returns an output appropriate to the input. To define that function, Lean uses a suitable well-founded measure. The internals are meant to be hidden from users; the canonical way to make use of such definitions is to use {leanRef}`simp` (or {tactic}`unfold`), as we did above.

这之所以成为相互定义，是因为 {leanRef}`even` 是根据 {leanRef}`odd` 递归定义的，而 {leanRef}`odd` 是根据 {leanRef}`even` 递归定义的。
在底层，这被编译为单个递归定义。内部定义的函数接受一个和类型的元素作为参数，该元素要么是 {leanRef}`even` 的输入，要么是 {leanRef}`odd` 的输入。
然后它返回适合输入的输出。为了定义该函数，Lean 使用适当的良基度量。
内部细节旨在对用户隐藏；使用此类定义的规范方法是使用 {leanRef}`simp`（或 {tactic}`unfold`），正如我们在上面所做的那样。

:::leanFirst
-- Mutual recursive definitions also provide natural ways of working with mutual and nested inductive types. Recall the definition of {leanRef}`Even` and {leanRef}`Odd` as mutual inductive predicates as presented before.

相互递归定义还提供了处理相互和嵌套归纳类型的自然方法。回想一下之前介绍的作为相互归纳谓词的 {leanRef}`Even` 和 {leanRef}`Odd` 的定义。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end
```
:::

:::leanFirst
-- The constructors, {leanRef}`even_zero`, {leanRef}`even_succ`, and {leanRef}`odd_succ` provide positive means for showing that a number is even or odd. We need to use the fact that the inductive type is generated by these constructors to know that zero is not odd, and that the latter two implications reverse. As usual, the constructors are kept in a namespace that is named after the type being defined, and the command {leanRef}`open Even Odd` allows us to access them more conveniently.

构造函数 {leanRef}`even_zero`、{leanRef}`even_succ` 和 {leanRef}`odd_succ` 提供了证明数字是偶数或奇数的积极手段。
我们需要使用归纳类型由这些构造函数生成的事实，才能知道零不是奇数，并且后两个蕴涵是可逆的。
像往常一样，构造函数保存在以定义的类型命名的命名空间中，命令 {leanRef}`open Even Odd` 允许我们更方便地访问它们。

```lean
mutual
 inductive Even : Nat → Prop where
   | even_zero : Even 0
   | even_succ : ∀ n, Odd n → Even (n + 1)
 inductive Odd : Nat → Prop where
   | odd_succ : ∀ n, Even n → Odd (n + 1)
end
------
open Even Odd

theorem not_odd_zero : ¬ Odd 0 :=
  fun h => nomatch h

theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
  | _, odd_succ n h => h

theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
  | _, even_succ n h => h
```
:::

-- For another example, suppose we use a nested inductive type to define a set of terms inductively, so that a term is either a constant (with a name given by a string), or the result of applying a constant to a list of constants.

再举一个例子，假设我们使用嵌套归纳类型来归纳定义一组项，使得一个项要么是一个常量（名称由字符串给出），要么是将一个常量应用于常量列表的结果。

```lean
inductive Term where
  | const : String → Term
  | app   : String → List Term → Term
```

-- We can then use a mutual recursive definition to count the number of constants occurring in a term, as well as the number occurring in a list of terms.

然后我们可以使用相互递归定义来计算项中出现的常量数量，以及项列表中出现的数量。

```lean
inductive Term where
 | const : String → Term
 | app   : String → List Term → Term
------
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

:::leanFirst
-- As a final example, we define a function {leanRef}`replaceConst a b e` that replaces a constant {leanRef (in := "replaceConst a b e")}`a` with {leanRef (in := "replaceConst a b e")}`b` in a term {leanRef (in := "replaceConst a b e")}`e`, and then prove the number of constants is the same. Note that, our proof uses mutual recursion (aka induction).

作为最后一个例子，我们定义一个函数 {leanRef}`replaceConst a b e`，它将项 {leanRef (in := "replaceConst a b e")}`e` 中的常量 {leanRef (in := "replaceConst a b e")}`a` 替换为 {leanRef (in := "replaceConst a b e")}`b`，然后证明常量的数量是相同的。
注意，我们的证明使用了相互递归（又名归纳）。

```lean
inductive Term where
 | const : String → Term
 | app   : String → List Term → Term
namespace Term
mutual
 def numConsts : Term → Nat
   | const _ => 1
   | app _ cs => numConstsLst cs
  def numConstsLst : List Term → Nat
   | [] => 0
   | c :: cs => numConsts c + numConstsLst cs
end
------
mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)

  def replaceConstLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end

mutual
  theorem numConsts_replaceConst (a b : String) (e : Term) :
      numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c =>
      simp [replaceConst]; split <;> simp [numConsts]
    | app f cs =>
      simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]

  theorem numConsts_replaceConstLst (a b : String) (es : List Term) :
      numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | [] => simp [replaceConstLst, numConstsLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
            numConsts_replaceConstLst a b cs]
end
```
:::

-- # Dependent Pattern Matching
# 依赖模式匹配
%%%
tag := "dependent-pattern-matching"
%%%


::::setup
```
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)

def map (f : α → β) : Vect α n → Vect β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (map f xs)

def zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

def unzip : Vect (α × β) n → (Vect α n × Vect β n)
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
    let (xs, ys) := unzip xys
    (.cons x xs, .cons y ys)

def tail : Vect α (n + 1) → Vect α n
  | .cons x xs => xs

variable {v : Vect α (n + 1)}
open Vect
```

:::leanFirst
-- All the examples of pattern matching we considered in the section on
-- {ref "pattern-matching"}[pattern matching] can easily be written using {lit}`casesOn`
-- and {lit}`recOn`. However, this is often not the case with indexed
-- inductive families such as {leanRef}`Vect α n`, since case splits impose
-- constraints on the values of the indices. Without the equation
-- compiler, we would need a lot of boilerplate code to define very
-- simple functions such as {lean}`map`, {lean}`zip`, and {lean}`unzip` using
-- recursors. To understand the difficulty, consider what it would take
-- to define a function {lean}`tail` which takes a vector
-- {lean}`v : Vect α (n + 1)` and deletes the first element.

我们在 {ref "pattern-matching"}[模式匹配] 一节中考虑的所有模式匹配示例都可以很容易地使用 {lit}`casesOn` 和 {lit}`recOn` 编写。
然而，对于像 {leanRef}`Vect α n` 这样的索引归纳族，情况通常并非如此，因为案例拆分会对索引的值施加约束。
如果没有方程编译器，我们需要大量的样板代码来使用递归器定义非常简单的函数，如 {lean}`map`、{lean}`zip` 和 {lean}`unzip`。
为了理解其中的困难，考虑定义一个函数 {lean}`tail` 需要什么，该函数接受一个向量 {lean}`v : Vect α (n + 1)` 并删除第一个元素。

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
```
:::



-- A first thought might be to use the {name}`Vect.casesOn` function:

首先想到的可能是使用 {name}`Vect.casesOn` 函数：

```signature
Vect.casesOn.{u, v}
  {α : Type v} {motive : (a : Nat) → Vect α a → Sort u}
  {a : Nat}
  (t : Vect α a)
  (nil : motive 0 nil)
  (cons : (a : α) → {n : Nat} → (a_1 : Vect α n) →
    motive (n + 1) (cons a a_1)) :
  motive a t
```


-- But what value should we return in the {name}`nil` case? Something funny
-- is going on: if {lean}`v` has type {lean}`Vect α (n + 1)`, it _can't_ be
-- {name}`nil`, but it is not clear how to tell that to {name}`Vect.casesOn`.

但是在 {name}`nil` 这种情况下我们应该返回什么值呢？有些奇怪的事情正在发生：如果 {lean}`v` 的类型是 {lean}`Vect α (n + 1)`，
它 _不能_ 是 {name}`nil`，但不清楚如何告诉 {name}`Vect.casesOn` 这一点。

::::

-- One solution is to define an auxiliary function:

一种解决方案是定义一个辅助函数：

```lean
set_option linter.unusedVariables false
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def tailAux (v : Vect α m) : m = n + 1 → Vect α n :=
  Vect.casesOn (motive := fun x _ => x = n + 1 → Vect α n) v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vect α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vect α (n+1)) : Vect α n :=
  tailAux v rfl
-----
end Vect
```

-- In the {leanRef}`nil` case, {leanRef (in := "m = n + 1")}`m` is instantiated to {leanRef}`0`, and
-- {leanRef}`Nat.noConfusion` makes use of the fact that {leanRef}`0 = n + 1` cannot
-- occur.  Otherwise, {leanRef}`v` is of the form {lit}`cons `{leanRef}`a`{lit}` `{leanRef}`as`, and we can simply
-- return {leanRef}`as`, after casting it from a vector of length {leanRef (in := "m + 1 = n + 1")}`m` to a
-- vector of length {leanRef (in := "m + 1= n + 1")}`n`.

在 {leanRef}`nil` 这种情况下，{leanRef (in := "m = n + 1")}`m` 被实例化为 {leanRef}`0`，{leanRef}`Nat.noConfusion` 利用了 {leanRef}`0 = n + 1` 不可能发生的事实。
否则，{leanRef}`v` 的形式为 {lit}`cons `{leanRef}`a`{lit}` `{leanRef}`as`，我们可以简单地返回 {leanRef}`as`，
在将其从长度为 {leanRef (in := "m + 1 = n + 1")}`m` 的向量转换为长度为 {leanRef (in := "m + 1= n + 1")}`n` 的向量之后。

-- The difficulty in defining {leanRef}`tail` is to maintain the relationships between the indices.
-- The hypothesis {leanRef}`m = n + 1` in {leanRef}`tailAux` is used to communicate the relationship
-- between {leanRef (in:="m = n + 1")}`n` and the index associated with the minor premise.
-- Moreover, the {leanRef}`0 = n + 1` case is unreachable, and the canonical way to discard such
-- a case is to use {leanRef}`Nat.noConfusion`.

定义 {leanRef}`tail` 的困难在于维护索引之间的关系。{leanRef}`tailAux` 中的假设 {leanRef}`m = n + 1` 用于传达 {leanRef (in:="m = n + 1")}`n` 与次要前提关联的索引之间的关系。
此外，{leanRef}`0 = n + 1` 的情况是不可达的，丢弃这种情况的规范方法是使用 {leanRef}`Nat.noConfusion`。

:::leanFirst
-- The {leanRef}`tail` function is, however, easy to define using recursive
-- equations, and the equation compiler generates all the boilerplate
-- code automatically for us. Here are a number of similar examples:

然而，{leanRef}`tail` 函数很容易使用递归方程定义，方程编译器会自动为我们生成所有样板代码。这里有许多类似的例子：

```lean
set_option linter.unusedVariables false
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def head : {n : Nat} → Vect α (n+1) → α
  | n, cons a as => a

def tail : {n : Nat} → Vect α (n+1) → Vect α n
  | n, cons a as => as

theorem eta : ∀ {n : Nat} (v : Vect α (n+1)), cons (head v) (tail v) = v
  | n, cons a as => rfl

def map (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : {n : Nat} → Vect α n → Vect β n → Vect (α × β) n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a, b) (zip as bs)
------
end Vect
```
:::

-- Note that we can omit recursive equations for “unreachable” cases such
-- as {leanRef}`head`{lit}` `{leanRef}`nil`. The automatically generated definitions for indexed
-- families are far from straightforward. For example:

注意，我们可以省略“不可达”情况（如 {leanRef}`head`{lit}` `{leanRef}`nil`）的递归方程。索引族的自动生成定义远非直截了当。例如：

```lean
set_option linter.unusedVariables false
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
-------
def zipWith (f : α → β → γ) : {n : Nat} → Vect α n → Vect β n → Vect γ n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (f a b) (zipWith f as bs)

#print zipWith
#print zipWith.match_1
------
end Vect
```

:::setup
```
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
```

-- The {leanRef}`zipWith` function is even more tedious to define by hand than the
-- {leanRef}`tail` function. We encourage you to try it, using {name}`Vect.recOn`,
-- {name}`Vect.casesOn` and {name}`Vect.noConfusion`.

{leanRef}`zipWith` 函数比 {leanRef}`tail` 函数更难手动定义。我们鼓励你尝试使用 {name}`Vect.recOn`、{name}`Vect.casesOn` 和 {name}`Vect.noConfusion` 来定义它。
:::

-- # Inaccessible Patterns
# 不可访问模式
%%%
tag := "inaccessible-patterns"
%%%

-- Sometimes an argument in a dependent matching pattern is not essential
-- to the definition, but nonetheless has to be included to specialize
-- the type of the expression appropriately. Lean allows users to mark
-- such subterms as _inaccessible_ for pattern matching. These
-- annotations are essential, for example, when a term occurring in the
-- left-hand side is neither a variable nor a constructor application,
-- because these are not suitable targets for pattern matching. We can
-- view such inaccessible patterns as “don't care” components of the
-- patterns. You can declare a subterm inaccessible by writing
-- {lit}`.(t)`. If the inaccessible pattern can be inferred, you can also write
-- {lit}`_`.

有时，依赖匹配模式中的参数对定义不是必不可少的，但仍然必须包含在内以适当地专门化表达式的类型。
Lean 允许用户将此类子项标记为 _不可访问_ 以进行模式匹配。
例如，当出现在左侧的项既不是变量也不是构造函数应用时，这些注释是必不可少的，因为这些不是模式匹配的合适目标。
我们可以将此类不可访问模式视为模式的“不关心”组件。
你可以通过编写 {lit}`.(t)` 将子项声明为不可访问。如果可以推断出不可访问模式，你也可以写 {lit}`_`。

:::leanFirst
-- The following example, we declare an inductive type that defines the
-- property of “being in the image of {leanRef (in := "(f :")}`f`”. You can view an element of
-- the type {leanRef}`ImageOf f b` as evidence that {leanRef (in := "ImageOf f b")}`b` is in the image of
-- {leanRef (in := "ImageOf f b")}`f`, whereby the constructor {leanRef}`imf` is used to build such
-- evidence. We can then define any function {leanRef (in := "inverse {f")}`f` with an “inverse”
-- which takes anything in the image of {leanRef (in := "inverse {f")}`f` to an element that is
-- mapped to it. The typing rules forces us to write {leanRef (in := ".(f a)")}`f a` for the
-- first argument, but this term is neither a variable nor a constructor
-- application, and plays no role in the pattern-matching definition. To
-- define the function {leanRef}`inverse` below, we _have to_ mark {leanRef (in := ".(f a)")}`f a`
-- inaccessible.

在下面的例子中，我们声明了一个归纳类型，它定义了“在 {leanRef (in := "(f :")}`f` 的像中”的属性。
你可以将类型 {leanRef}`ImageOf f b` 的元素视为 {leanRef (in := "ImageOf f b")}`b` 在 {leanRef (in := "ImageOf f b")}`f` 的像中的证据，
其中构造函数 {leanRef}`imf` 用于构建此类证据。然后我们可以定义任何具有“逆”的函数 {leanRef (in := "inverse {f")}`f`，
该逆函数将 {leanRef (in := "inverse {f")}`f` 像中的任何内容映射到映射到它的元素。
类型规则强制我们为第一个参数编写 {leanRef (in := ".(f a)")}`f a`，但该项既不是变量也不是构造函数应用，
并且在模式匹配定义中不起作用。为了定义下面的函数 {leanRef}`inverse`，我们 _必须_ 将 {leanRef (in := ".(f a)")}`f a` 标记为不可访问。

```lean
inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a
```
:::

-- In the example above, the inaccessible annotation makes it clear that
-- {leanRef (in := ".(f a)")}`f` is _not_ a pattern matching variable.

在上面的例子中，不可访问注释清楚地表明 {leanRef (in := ".(f a)")}`f` _不是_ 模式匹配变量。

:::leanFirst
-- Inaccessible patterns can be used to clarify and control definitions that
-- make use of dependent pattern matching. Consider the following
-- definition of the function {leanRef}`Vect.add`, which adds two vectors of
-- elements of a type, assuming that type has an associated addition
-- function:

不可访问模式可用于阐明和控制使用依赖模式匹配的定义。考虑函数 {leanRef}`Vect.add` 的以下定义，
它将某种类型的元素的两个向量相加，假设该类型具有关联的加法函数：

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)

def Vect.add [Add α] : {n : Nat} → Vect α n → Vect α n → Vect α n
  | 0,   nil,       nil       => nil
  | n+1, cons a as, cons b bs => cons (a + b) (add as bs)
```
:::

-- The argument {leanRef}`{n : Nat}` appear after the colon, because it cannot
-- be held fixed throughout the definition.  When implementing this
-- definition, the equation compiler starts with a case distinction as to
-- whether the first argument is {leanRef}`0` or of the form {leanRef}`n+1`.  This is
-- followed by nested case splits on the next two arguments, and in each
-- case the equation compiler rules out the cases are not compatible with
-- the first pattern.

参数 {leanRef}`{n : Nat}` 出现在冒号之后，因为它不能在整个定义中保持固定。在实现此定义时，
方程编译器首先区分第一个参数是 {leanRef}`0` 还是 {leanRef}`n+1` 的形式。
接下来是对接下来的两个参数进行嵌套案例拆分，并且在每种情况下，方程编译器都会排除与第一个模式不兼容的情况。

-- But, in fact, a case split is not required on the first argument; the
-- {lit}`casesOn` eliminator for {leanRef}`Vect` automatically abstracts this
-- argument and replaces it by {leanRef}`0` and {leanRef}`n + 1` when we do a case
-- split on the second argument. Using inaccessible patterns, we can prompt
-- the equation compiler to avoid the case split on {leanRef}`n`.

但实际上，第一个参数不需要案例拆分；当我们对第二个参数进行案例拆分时，{leanRef}`Vect` 的 {lit}`casesOn` 消除器会自动抽象此参数并将其替换为 {leanRef}`0` 和 {leanRef}`n + 1`。
使用不可访问模式，我们可以提示方程编译器避免对 {leanRef}`n` 进行案例拆分。

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def add [Add α] : {n : Nat} → Vect α n → Vect α n → Vect α n
  | .(_), nil,       nil       => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)
-------
end Vect
```

-- Marking the position as an inaccessible pattern tells the
-- equation compiler first, that the form of the argument should be
-- inferred from the constraints posed by the other arguments, and,
-- second, that the first argument should _not_ participate in pattern
-- matching.

将位置标记为不可访问模式首先告诉方程编译器，参数的形式应该从其他参数施加的约束中推断出来，
其次，第一个参数 _不_ 应该参与模式匹配。

-- The inaccessible pattern {leanRef}`.(_)` can be written as {lit}`_` for convenience.

为了方便起见，不可访问模式 {leanRef}`.(_)` 可以写成 {lit}`_`。

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def add [Add α] : {n : Nat} → Vect α n → Vect α n → Vect α n
  | _, nil,       nil       => nil
  | _, cons a as, cons b bs => cons (a + b) (add as bs)
-------
end Vect
```

-- As we mentioned above, the argument {leanRef}`{n : Nat}` is part of the
-- pattern matching, because it cannot be held fixed throughout the
-- definition. Rather than requiring that these discriminants be provided explicitly, Lean implicitly includes
-- these extra discriminants automatically for us.

正如我们上面提到的，参数 {leanRef}`{n : Nat}` 是模式匹配的一部分，因为它不能在整个定义中保持固定。
Lean 不要求显式提供这些判别式，而是自动为我们隐式包含这些额外的判别式。

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def add [Add α] {n : Nat} : Vect α n → Vect α n → Vect α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
-------
end Vect
```

-- When combined with the _auto bound implicits_ feature, you can simplify
-- the declare further and write:

当与 _自动绑定隐式_ 功能结合使用时，你可以进一步简化声明并编写：

```lean
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def add [Add α] : Vect α n → Vect α n → Vect α n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)
-------
end Vect
```

-- Using these new features, you can write the other vector functions defined
-- in the previous sections more compactly as follows:

使用这些新功能，你可以更紧凑地编写前面部分中定义的其他向量函数，如下所示：

```lean
set_option linter.unusedVariables false
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n+1)
namespace Vect
------
def head : Vect α (n+1) → α
  | cons a as => a

def tail : Vect α (n+1) → Vect α n
  | cons a as => as

theorem eta : (v : Vect α (n+1)) → cons (head v) (tail v) = v
  | cons a as => rfl

def map (f : α → β → γ) : Vect α n → Vect β n → Vect γ n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (f a b) (map f as bs)

def zip : Vect α n → Vect β n → Vect (α × β) n
  | nil,       nil       => nil
  | cons a as, cons b bs => cons (a, b) (zip as bs)
-------
end Vect
```

-- # Match Expressions
# 匹配表达式
%%%
tag := "match-expressions"
%%%

-- Lean also provides a compiler for {kw}`match`-{kw}`with` expressions found in
-- many functional languages:

Lean 还为许多函数式语言中常见的 {kw}`match`-{kw}`with` 表达式提供了编译器：

```lean
set_option linter.unusedVariables false
------
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0     => false
  | n + 1 => true
```

-- This does not look very different from an ordinary pattern matching
-- definition, but the point is that a {kw}`match` can be used anywhere in
-- an expression, and with arbitrary arguments.

这看起来与普通的模式匹配定义没有太大区别，但重点是 {kw}`match` 可以在表达式的任何地方使用，并且可以使用任意参数。

```lean
set_option linter.unusedVariables false
-------
def isNotZero (m : Nat) : Bool :=
  match m with
  | 0     => false
  | n + 1 => true

def filter (p : α → Bool) : List α → List α
  | []      => []
  | a :: as =>
    match p a with
    | true => a :: filter p as
    | false => filter p as

example : filter isNotZero [1, 0, 0, 3, 0] = [1, 3] := rfl
```

-- Here is another example:

这里有另一个例子：

```lean
def foo (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,     true  => 0
      | m + 1, true  => m + 7
      | 0,     false => 5
      | m + 1, false => m + 3

#eval foo 7 true false

example : foo 7 true false = 9 := rfl
```

-- Lean uses the {kw}`match` construct internally to implement pattern-matching in all parts of the system.
-- Thus, all four of these definitions have the same net effect:

Lean 在内部使用 {kw}`match` 构造来实现系统所有部分的模式匹配。因此，这四个定义具有相同的净效果：

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

-- These variations are equally useful for destructing propositions:

这些变体对于解构命题同样有用：

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

-- # Exercises
# 练习
%%%
tag := "induction-and-recursion-exercises"
%%%

```setup

open List

variable {xs : List α} {n : Nat}

```

-- 1. Open a namespace {lit}`Hidden` to avoid naming conflicts, and use the
--    equation compiler to define addition, multiplication, and
--    exponentiation on the natural numbers. Then use the equation
--    compiler to derive some of their basic properties.

1. 打开一个命名空间 {lit}`Hidden` 以避免命名冲突，并使用方程编译器定义自然数上的加法、乘法和幂运算。
   然后使用方程编译器推导它们的一些基本属性。

-- 2. Similarly, use the equation compiler to define some basic
--    operations on lists (like the {lean}`reverse` function) and prove
--    theorems about lists by induction (such as the fact that
--    {lean}`reverse (reverse xs) = xs` for any list {lean}`xs`).

2. 类似地，使用方程编译器定义列表上的一些基本操作（如 {lean}`reverse` 函数），并通过归纳法证明关于列表的定理（例如对于任何列表 {lean}`xs`，{lean}`reverse (reverse xs) = xs`）。

-- 3. Define your own function to carry out course-of-value recursion on
--    the natural numbers. Similarly, see if you can figure out how to
--    define {name}`WellFounded.fix` on your own.

3. 定义你自己的函数来对自然数执行值域递归。同样，看看你是否能弄清楚如何自己定义 {name}`WellFounded.fix`。

-- 4. Following the examples in the section on {ref "dependent-pattern-matching"}[dependent pattern matching],
--    define a function that will append two vectors.
--    This is tricky; you will have to define an auxiliary function.

4. 按照 {ref "dependent-pattern-matching"}[依赖模式匹配] 一节中的示例，定义一个将两个向量连接起来的函数。
   这很棘手；你必须定义一个辅助函数。



5.  :::leanFirst
--     Consider the following type of arithmetic expressions. The idea is
--     that {leanRef}`var`{lit}` `{lean}`n` is a variable, {lit}`vₙ`, and {leanRef}`const`{lit}` `{lean}`n` is the
--     constant whose value is {lean}`n`.
    考虑以下算术表达式类型。其思想是 {leanRef}`var`{lit}` `{lean}`n` 是一个变量 {lit}`vₙ`，而 {leanRef}`const`{lit}` `{lean}`n` 是值为 {lean}`n` 的常数。

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
    :::

    -- Here {leanRef}`sampleExpr` represents {lit}`(v₀ * 7) + (2 * v₁)`.

    这里 {leanRef}`sampleExpr` 表示 {lit}`(v₀ * 7) + (2 * v₁)`。

    -- Write a function that evaluates such an expression, evaluating each {leanRef}`var n` to {leanRef}`v n`.

    :::leanFirst
    编写一个函数来计算这样的表达式，将每个 {leanRef}`var n` 计算为 {leanRef}`v n`。

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
    ------
    def eval (v : Nat → Nat) : Expr → Nat
      | const n     => sorry
      | var n       => v n
      | plus e₁ e₂  => sorry
      | times e₁ e₂ => sorry

    def sampleVal : Nat → Nat
      | 0 => 5
      | 1 => 6
      | _ => 0

    -- 试一试。你应该在这里得到 47。
    -- #eval eval sampleVal sampleExpr
    ```
    :::

    -- Implement “constant fusion,” a procedure that simplifies subterms like
    -- {lean}`5 + 7` to {lean}`12`. Using the auxiliary function {leanRef}`simpConst`,
    -- define a function “fuse”: to simplify a plus or a times, first
    -- simplify the arguments recursively, and then apply {leanRef}`simpConst` to
    -- try to simplify the result.

    :::leanFirst
    实现“常量融合”，这是一个将子项（如 {lean}`5 + 7`）简化为 {lean}`12` 的过程。使用辅助函数 {leanRef}`simpConst`，定义一个函数“fuse”：为了简化加法或乘法，首先递归地简化参数，然后应用 {leanRef}`simpConst` 尝试简化结果。

    ```lean
    inductive Expr where
      | const : Nat → Expr
      | var : Nat → Expr
      | plus : Expr → Expr → Expr
      | times : Expr → Expr → Expr
      deriving Repr
    open Expr
    def eval (v : Nat → Nat) : Expr → Nat
      | const n     => sorry
      | var n       => v n
      | plus e₁ e₂  => sorry
      | times e₁ e₂ => sorry
    ------
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
    :::

    -- The last two theorems show that the definitions preserve the value.

    最后两个定理表明这些定义保留了值。
