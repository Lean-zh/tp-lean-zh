import VersoManual

import TPiLZh.Examples

open TPiLZh

open Verso.Genre Manual

#doc (Manual) "依值类型论" =>
%%%
file := "DependentTypeTheory"
tag := "dependent-type-theory"
htmlSplit := .never
%%%

-- Dependent type theory is a powerful and expressive language, allowing
-- you to express complex mathematical assertions, write complex hardware
-- and software specifications, and reason about both of these in a
-- natural and uniform way. Lean is based on a version of dependent type
-- theory known as the _Calculus of Constructions_, with a countable
-- hierarchy of non-cumulative universes and inductive types. By the end
-- of this chapter, you will understand much of what this means.

依值类型论（Dependent type theory）是一种强大而富有表达力的语言，允许你表达复杂的数学断言，
编写复杂的硬件和软件规范，并以自然和统一的方式对这两者进行推理。
Lean 是基于一个被称为 _构造演算（Calculus of Constructions）_ 的依值类型论的版本，
它拥有一个可数的非累积性宇宙（non-cumulative universe）的层次结构以及归纳类型（Inductive type）。
在本章结束时，你将学会一大部分。

-- # Simple Type Theory
# 简单类型论
%%%
tag := "simple-type-theory"
%%%

-- “Type theory” gets its name from the fact that every expression has an
-- associated _type_. For example, in a given context, {lit}`x + 0` may
-- denote a natural number and {lit}`f` may denote a function on the natural
-- numbers. For those who like precise definitions, a Lean natural number
-- is an arbitrary-precision unsigned integer.

“类型论”得名于其中每个表达式都有一个关联的 _类型_。
例如，在一个给定的语境中，{lit}`x + 0` 可能表示一个自然数，{lit}`f` 可能表示一个定义在自然数上的函数。
对于那些喜欢精确定义的人来说，Lean 中的自然数是任意精度的无符号整数。

-- Here are some examples of how you can declare objects in Lean and
-- check their types.

这里的一些例子展示了如何声明对象以及检查其类型。

/-
```lean
/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- m : Nat
#check n
#check n + 0        -- n + 0 : Nat
#check m * (n + 0)  -- m * (n + 0) : Nat
#check b1           -- b1 : Bool
-- "&&" is the Boolean and
#check b1 && b2     -- b1 && b2 : Bool
-- Boolean or
#check b1 || b2     -- b1 || b2 : Bool
-- Boolean "true"
#check true         -- Bool.true : Bool

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```
-/

```lean
/- 定义一些常数 -/

def m : Nat := 1       -- m 是自然数
def n : Nat := 0
def b1 : Bool := true  -- b1 是布尔型
def b2 : Bool := false

/- 检查类型 -/

#check m            -- m : Nat
#check n
#check n + 0        -- n + 0 : Nat
#check m * (n + 0)  -- m * (n + 0) : Nat
#check b1           -- b1 : Bool
-- "&&" 是布尔与
#check b1 && b2     -- b1 && b2 : Bool
-- 布尔或
#check b1 || b2     -- b1 || b2 : Bool
-- 布尔 "真"
#check true         -- Bool.true : Bool
/- 求值（Evaluate） -/
#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```

-- Any text between {lit}`/-` and {lit}`-/` constitutes a comment block that is
-- ignored by Lean. Similarly, two dashes {lean}`--` indicate that the rest of
-- the line contains a comment that is also ignored. Comment blocks can
-- be nested, making it possible to “comment out” chunks of code, just as
-- in many programming languages.

位于 {lit}`/-` 和 {lit}`-/` 之间的文本组成了一个注释块，会被 Lean 忽略。
类似地，两条横线 {lean}`--` 表示该行的其余部分包含也会被忽略的注释。
注释块可以嵌套，这样就可以“注释掉”一整块代码，这和许多编程语言都是一样的。

-- The {kw}`def` keyword declares new constant symbols into the
-- working environment. In the example above, {leanRef}`def m : Nat := 1`
-- defines a new constant {leanRef}`m` of type {lean}`Nat` whose value is {leanRef}`1`.
-- The {kw}`#check` command asks Lean to report their
-- types; in Lean, auxiliary commands that query the system for
-- information typically begin with the hash (#) symbol.
-- The {kw}`#eval` command asks Lean to evaluate the given expression.
-- You should try
-- declaring some constants and type checking some expressions on your
-- own. Declaring new objects in this manner is a good way to experiment
-- with the system.

{kw}`def` 关键字声明工作环境中的新常量符号。在上面的例子中，{leanRef}`def m : Nat := 1`
定义了一个 {lean}`Nat` 类型的新常量 {leanRef}`m`，其值为 {leanRef}`1`。
{kw}`#check` 命令要求 Lean 报告它们的类型；在 Lean 中，用于向系统询问信息的辅助命令通常都以井号 (#) 开头。
{kw}`#eval` 命令让 Lean 计算给出的表达式。
你应该试试自己声明一些常量和检查一些表达式的类型。以这种方式声明新对象是试验系统的好方法。

:::setup
```
variable (a b : Type)
```
-- What makes simple type theory powerful is that you can build new types
-- out of others. For example, if {lean}`a` and {lean}`b` are types, {lean}`a -> b`
-- denotes the type of functions from {lean}`a` to {lean}`b`, and {lean}`a × b`
-- denotes the type of pairs consisting of an element of {lean}`a` paired
-- with an element of {lean}`b`, also known as the _Cartesian product_. Note
-- that {lit}`×` is a Unicode symbol. The judicious use of Unicode improves
-- legibility, and all modern editors have great support for it. In the
-- Lean standard library, you often see Greek letters to denote types,
-- and the Unicode symbol {lit}`→` as a more compact version of {lit}`->`.
:::

简单类型论的强大之处在于，你可以从其他类型中构建新的类型。例如，如果 {lean}`a` 和 {lean}`b` 是类型，{lean}`a -> b`
表示从 {lean}`a` 到 {lean}`b` 的函数类型，{lean}`a × b`
表示由 {lean}`a` 元素与 {lean}`b` 元素配对构成的类型，也称为 _笛卡尔积_。注意
{lit}`×` 是一个 Unicode 符号。合理使用 Unicode 提高了易读性，所有现代编辑器都支持它。在
Lean 标准库中，你经常看到希腊字母表示类型，Unicode 符号 {lit}`→` 是 {lit}`->` 的更紧凑版本。
:::

/-
```lean (check := false)
#check Nat → Nat      -- type the arrow as “\to” or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"
```
```lean
#check Nat.succ     -- Nat.succ (n : Nat) : Nat
#check (0, 1)       -- (0, 1) : Nat × Nat
#check Nat.add      -- Nat.add : Nat → Nat → Nat

#check Nat.succ 2   -- Nat.succ 2 : Nat
#check Nat.add 3    -- Nat.add 3 : Nat → Nat
#check Nat.add 5 2  -- Nat.add 5 2 : Nat
#check (5, 9).1     -- (5, 9).fst : Nat
#check (5, 9).2     -- (5, 9).snd : Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```
-/

```lean (check := false)
#check Nat → Nat      -- 用“\to” or "\r"来打出这个箭头
#check Nat -> Nat     -- 也可以用 ASCII 符号

#check Nat × Nat      -- 用"\times"打出乘号
#check Prod Nat Nat   -- 换成 ASCII 符号

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  -- 结果和上一个一样

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- 一个“泛函”
```
```lean
#check Nat.succ     -- Nat.succ (n : Nat) : Nat
#check (0, 1)       -- (0, 1) : Nat × Nat
#check Nat.add      -- Nat.add : Nat → Nat → Nat

#check Nat.succ 2   -- Nat.succ 2 : Nat
#check Nat.add 3    -- Nat.add 3 : Nat → Nat
#check Nat.add 5 2  -- Nat.add 5 2 : Nat
#check (5, 9).1     -- (5, 9).fst : Nat
#check (5, 9).2     -- (5, 9).snd : Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```

-- Once again, you should try some examples on your own.

同样，你应该自己尝试一些例子。

-- Let's take a look at some basic syntax. You can enter the Unicode
-- arrow {lit}`→` by typing {kbd}`\to` or {kbd}`\r` or {kbd}`\->`. You can also use the
-- ASCII alternative {lit}`->`, so the expressions {lean}`Nat -> Nat` and {lean}`Nat → Nat`
-- mean the same thing. Both expressions denote the type of
-- functions that take a natural number as input and return a natural
-- number as output. The Unicode symbol {lit}`×` for the Cartesian product
-- is entered as {kbd}`\times`. You will generally use lower-case Greek
-- letters like {lit}`α`, {lit}`β`, and {lit}`γ` to range over types. You can
-- enter these particular ones with {kbd}`\a`, {kbd}`\b`, and {kbd}`\g`.

让我们看一些基本语法。你可以通过输入 {kbd}`\to` 或者 {kbd}`\r` 或者 {kbd}`\->` 来输入 Unicode 箭头 {lit}`→`。
你也可以使用 ASCII 替代符号 {lit}`->`，所以表达式 {lean}`Nat -> Nat` 和 {lean}`Nat → Nat`
意思是一样的。这两个表达式都表示以一个自然数作为输入并返回一个自然数作为输出的函数类型。
Unicode 符号 {lit}`×` 是笛卡尔积，用 {kbd}`\times` 输入。通常使用小写的希腊字母
如 {lit}`α`，{lit}`β`，和 {lit}`γ` 来表示类型变量。你可以
用 {kbd}`\a`，{kbd}`\b`，和 {kbd}`\g` 来输入它们。

::::setup
```
variable (α β : Type) (f : α → β) (x : α) (m n : Nat) (p : Nat × Nat)
```
-- There are a few more things to notice here. First, the application of
-- a function {lean}`f` to a value {lean}`x` is denoted {lean}`f x` (e.g., {lean}`Nat.succ 2`).
-- Second, when writing type expressions, arrows associate to the _right_; for
-- example, the type of {lean}`Nat.add` is {lean}`Nat → Nat → Nat` which is equivalent
-- to {lean}`Nat → (Nat → Nat)`. Thus you can
-- view {lean}`Nat.add` as a function that takes a natural number and returns
-- another function that takes a natural number and returns a natural
-- number. In type theory, this is generally more convenient than
-- writing {lean}`Nat.add` as a function that takes a pair of natural numbers as
-- input and returns a natural number as output. For example, it allows
-- you to “partially apply” the function {lean}`Nat.add`.  The example above shows
-- that {lean}`Nat.add 3` has type {lean}`Nat → Nat`, that is, {lean}`Nat.add 3` returns a
-- function that “waits” for a second argument, {lean}`n`, which is then
-- equivalent to writing {lean}`Nat.add 3 n`.
:::comment
```
<!-- Taking a function ``h`` of type ``Nat
× Nat → Nat`` and “redefining” it to look like ``g`` is a process
known as _currying_. -->
```
:::

这里还有一些需要注意的事情。第一，函数 {lean}`f` 应用到值 {lean}`x` 上写为 {lean}`f x`（例如，{lean}`Nat.succ 2`）。
第二，当写类型表达式时，箭头是 _右结合_ 的；例如，
{lean}`Nat.add` 的类型是 {lean}`Nat → Nat → Nat`，等价于
{lean}`Nat → (Nat → Nat)`。因此你可以
把 {lean}`Nat.add` 看作一个函数，它接受一个自然数并返回
另一个函数，该函数接受一个自然数并返回一个自然数。
在类型论中，这通常比把 {lean}`Nat.add` 写成接受一对自然数作为
输入并返回一个自然数作为输出的函数更方便。例如，它允许
你“部分应用”函数 {lean}`Nat.add`。上面的例子显示
{lean}`Nat.add 3` 具有类型 {lean}`Nat → Nat`，即 {lean}`Nat.add 3` 返回一个
“等待”第二个参数 {lean}`n` 的函数，然后
等价于写 {lean}`Nat.add 3 n`。
:::comment
```
<!-- Taking a function ``h`` of type ``Nat
× Nat → Nat`` and “redefining” it to look like ``g`` is a process
known as _currying_. -->
```
:::

-- You have seen that if you have {lean}`m : Nat` and {lean}`n : Nat`, then
-- {lean}`(m, n)` denotes the ordered pair of {lean}`m` and {lean}`n` which is of
-- type {lean}`Nat × Nat`. This gives you a way of creating pairs of natural
-- numbers. Conversely, if you have {lean}`p : Nat × Nat`, then you can write
-- {lean}`p.1 : Nat` and {lean}`p.2 : Nat`. This gives you a way of extracting
-- its two components.
::::

你已经看到，如果你有 {lean}`m : Nat` 和 {lean}`n : Nat`，那么
{lean}`(m, n)` 表示 {lean}`m` 和 {lean}`n` 的有序对，其类型为
{lean}`Nat × Nat`。这为你提供了一种创建自然数对的方法。
反过来，如果你有 {lean}`p : Nat × Nat`，那么你可以写
{lean}`p.1 : Nat` 和 {lean}`p.2 : Nat`。这为你提供了一种提取
其两个分量的方法。
::::

-- # Types as objects
# 类型作为对象
%%%
tag := "types-as-objects"
%%%

-- One way in which Lean's dependent type theory extends simple type
-- theory is that types themselves—entities like {lean}`Nat` and {lean}`Bool`—are first-class citizens, which is to say that they themselves are
-- objects. For that to be the case, each of them also has to have a
-- type.

Lean 的依值类型论扩展简单类型论的一种方式是，类型本身——像 {lean}`Nat` 和 {lean}`Bool` 这样的实体——是一等公民，也就是说它们本身也是
对象。为了做到这一点，它们中的每一个也必须有一个
类型。

```lean
#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

-- You can see that each one of the expressions above is an object of
-- type {lean}`Type`. You can also declare new constants for types:

你可以看到上面的每个表达式都是类型为 {lean}`Type` 的对象。你也可以为类型声明新的常量：

```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- α : Type
#check F α      -- F α : Type
#check F Nat    -- F Nat : Type
#check G α      -- G α : Type → Type
#check G α β    -- G α β : Type
#check G α Nat  -- G α Nat : Type
```

-- As the example above suggests, you have already seen an example of a function of type
-- {lean}`Type → Type → Type`, namely, the Cartesian product {lean}`Prod`:

正如上面的例子所示，你已经看到了一个类型为
{lean}`Type → Type → Type` 的函数示例，即笛卡尔积 {lean}`Prod`：

```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- α × β : Type
#check α × β          -- α × β : Type

#check Prod Nat Nat   -- Nat × Nat : Type
#check Nat × Nat      -- Nat × Nat : Type
```

:::leanFirst
-- Here is another example: given any type {leanRef}`α`, the type {leanRef}`List α`
-- denotes the type of lists of elements of type {leanRef}`α`.

这里有另一个例子：给定任意类型 {leanRef}`α`，类型 {leanRef}`List α`
表示类型为 {leanRef}`α` 的元素的列表类型。

```lean
def α : Type := Nat

#check List α    -- List α : Type
#check List Nat  -- List Nat : Type
```
:::

-- Given that every expression in Lean has a type, it is natural to ask:
-- what type does {lean}`Type` itself have?

既然 Lean 中的每个表达式都有一个类型，那么很自然地会问：
{lean}`Type` 本身有什么类型？

```lean
#check Type      -- Type : Type 1
```

-- You have actually come up against one of the most subtle aspects of
-- Lean's typing system. Lean's underlying foundation has an infinite
-- hierarchy of types:

你实际上已经遇到了 Lean 类型系统中最微妙的方面之一。
Lean 的底层基础有一个无限的类型层次结构：

```lean
#check Type     -- Type : Type 1
#check Type 1   -- Type 1 : Type 2
#check Type 2   -- Type 2 : Type 3
#check Type 3   -- Type 3 : Type 4
#check Type 4   -- Type 4 : Type 5
```

:::setup
```
universe n
variable (n : Nat)
```
-- Think of {lean}`Type 0` as a universe of “small” or “ordinary” types.
-- {lean}`Type 1` is then a larger universe of types, which contains {lean}`Type 0`
-- as an element, and {lean}`Type 2` is an even larger universe of types,
-- which contains {lean}`Type 1` as an element. The list is infinite:
-- there is a {lean}`Type n` for every natural number {lean}`n`. {lean}`Type` is
-- an abbreviation for {lean}`Type 0`:
:::

可以将 {lean}`Type 0` 想象成一个由“小”或“普通”类型组成的宇宙。
{lean}`Type 1` 则是一个更大的类型宇宙，它包含 {lean}`Type 0`
作为一个元素，而 {lean}`Type 2` 是一个更大的类型宇宙，
它包含 {lean}`Type 1` 作为一个元素。这个列表是无限的：
对于每个自然数 {lean}`n` 都有一个 {lean}`Type n`。{lean}`Type` 是
{lean}`Type 0` 的缩写：
:::

```lean
#check Type
#check Type 0
```


-- The following table may help concretize the relationships being discussed.
-- Movement along the x-axis represents a change in the universe, while movement
-- along the y-axis represents a change in what is sometimes referred to as
-- “degree”.

下表可能有助于具体化所讨论的关系。
沿 x 轴的移动代表宇宙的变化，而沿 y 轴的移动
代表有时被称为“度”的变化。

:::table

*
 * sort
 * {lean}`Prop` ({lean}`Sort 0`)
 * {lean}`Type` ({lean}`Sort 1`)
 * {lean}`Type 1` ({lean}`Sort 2`)
 * {lean}`Type 2` ({lean}`Sort 3`)
 * ...

*
 * type
 * {lean}`True`
 * {lean}`Bool`
 * {lean}`Nat -> Type`
 * {lean}`Type -> Type 1`
 * ...

*
 * term
 * {lean}`True.intro`
 * {lean}`true`
 * {lean}`fun n => Fin n`
 * {lean}`fun (_ : Type) => Type`
 * ...

:::

:::setup

```
universe u
variable (α : Type u)
```

-- Some operations, however, need to be _polymorphic_ over type
-- universes. For example, {lean}`List α` should make sense for any type
-- {lean}`α`, no matter which type universe {lean}`α` lives in. This explains the
-- type signature of the function {lean}`List`:

然而，有些操作需要在类型宇宙上具有 _多态性_。例如，{lean}`List α` 应该对任何类型
{lean}`α` 都有意义，无论 {lean}`α` 存在于哪个类型宇宙中。这解释了
函数 {lean}`List` 的类型签名：


```lean
#check List    -- List.{u} (α : Type u) : Type u
```

-- Here {lit}`u` is a variable ranging over type levels. The output of the
-- {kw}`#check` command means that whenever {lean}`α` has type {lean}`Type u`,
-- {lean}`List α` also has type {lean}`Type u`. The function {lean}`Prod` is
-- similarly polymorphic:
:::

这里 {lit}`u` 是一个遍历类型级别的变量。
{kw}`#check` 命令的输出意味着只要 {lean}`α` 具有类型 {lean}`Type u`，
{lean}`List α` 也具有类型 {lean}`Type u`。函数 {lean}`Prod` 具有
类似的多态性：
:::

```lean
#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
```

-- To define polymorphic constants, Lean allows you to
-- declare universe variables explicitly using the {kw}`universe` command:

为了定义多态常量，Lean 允许你
使用 {kw}`universe` 命令显式声明宇宙变量：

```lean
universe u

def F (α : Type u) : Type u := Prod α α

#check F    -- F.{u} (α : Type u) : Type u
```

:::leanFirst
-- You can avoid the {kw}`universe` command by providing the universe parameters when defining {leanRef}`F`:

你可以通过在定义 {leanRef}`F` 时提供宇宙参数来避免使用 {kw}`universe` 命令：

```lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- F.{u} (α : Type u) : Type u
```
:::

-- # Function Abstraction and Evaluation
# 函数抽象和求值
%%%
tag := "function-abstraction-and-evaluation"
%%%

-- Lean provides a {kw}`fun` (or {kw}`λ`) keyword to create a function
-- from an expression as follows:

Lean 提供了一个 {kw}`fun`（或 {kw}`λ`）关键字，用于从表达式创建函数，如下所示：

```lean
#check fun (x : Nat) => x + 5   -- fun x => x + 5 : Nat → Nat
-- λ 和 fun 意思相同
#check λ (x : Nat) => x + 5     -- fun x => x + 5 : Nat → Nat
```

-- The type {lean}`Nat` can be inferred in this example:
在这个例子中，类型 {lean}`Nat` 可以被推断出来：
```lean
#check fun x => x + 5   -- fun x => x + 5 : Nat → Nat
#check λ x => x + 5     -- fun x => x + 5 : Nat → Nat
```

-- You can evaluate a lambda function by passing the required parameters:

你可以通过传递所需的参数来计算 lambda 函数：

```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

:::setup
```
variable {x : α} {t : β}
```

-- Creating a function from another expression is a process known as
-- _lambda abstraction_. Suppose you have the variable {lean}`x : α` and you can
-- construct an expression {lean}`t : β`, then the expression {lean}`fun (x : α) => t`,
-- or, equivalently, {lean}`λ (x : α) => t`, is an object of type {lean}`α → β`. Think of
-- this as the function from {lean}`α` to {lean}`β` which maps
-- any value {leanRef}`x` to the value {leanRef}`t`.
:::

从另一个表达式创建函数的过程称为
_lambda 抽象_。假设你有变量 {lean}`x : α` 并且你可以
构造一个表达式 {lean}`t : β`，那么表达式 {lean}`fun (x : α) => t`，
或者等价地，{lean}`λ (x : α) => t`，是一个类型为 {lean}`α → β` 的对象。可以把
这看作是从 {lean}`α` 到 {lean}`β` 的函数，它将
任何值 {leanRef}`x` 映射到值 {leanRef}`t`。
:::

-- Here are some more examples

这里还有一些例子

```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- fun x y => if (!y) = true then x + 1 else x + 2 : Nat → Bool → Nat
```

-- Lean interprets the final three examples as the same expression; in
-- the last expression, Lean infers the type of {leanRef}`x` and {leanRef}`y` from the
-- expression {leanRef}`if not y then x + 1 else x + 2`.

Lean 将最后三个例子解释为相同的表达式；在
最后一个表达式中，Lean 从表达式 {leanRef}`if not y then x + 1 else x + 2`
推断出 {leanRef}`x` 和 {leanRef}`y` 的类型。

-- Some mathematically common examples of operations of functions can be
-- described in terms of lambda abstraction:

一些数学上常见的函数运算示例可以用 lambda 抽象来描述：

```lean
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- fun x => x : Nat → Nat
#check fun x : Nat => true     -- fun x => true : Nat → Bool
#check fun x : Nat => g (f x)  -- fun x => g (f x) : Nat → Bool
#check fun x => g (f x)        -- fun x => g (f x) : Nat → Bool
```

-- Think about what these expressions mean. The expression
-- {lean}`fun x : Nat => x` denotes the identity function on {lean}`Nat`, the
-- expression {lean}`fun x : Nat => true` denotes the constant function that
-- always returns {lean}`true`, and {leanRef}`fun x : Nat => g (f x)` denotes the
-- composition of {leanRef}`f` and {leanRef}`g`.  You can, in general, leave off the
-- type annotation and let Lean infer it for you.  So, for example, you
-- can write {leanRef}`fun x => g (f x)` instead of {leanRef}`fun x : Nat => g (f x)`.

思考一下这些表达式的含义。表达式
{lean}`fun x : Nat => x` 表示 {lean}`Nat` 上的恒等函数，
表达式 {lean}`fun x : Nat => true` 表示总是返回 {lean}`true` 的常数函数，
而 {leanRef}`fun x : Nat => g (f x)` 表示 {leanRef}`f` 和 {leanRef}`g` 的复合。
通常，你可以省略类型注释，让 Lean 为你推断。因此，例如，你
可以写 {leanRef}`fun x => g (f x)` 而不是 {leanRef}`fun x : Nat => g (f x)`。

:::leanFirst
-- You can pass functions as parameters and by giving them names {leanRef}`f`
-- and {leanRef}`g` you can then use those functions in the implementation:

你可以将函数作为参数传递，通过给它们命名 {leanRef}`f`
和 {leanRef}`g`，你可以在实现中使用这些函数：

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
```
:::

-- You can also pass types as parameters:

你也可以将类型作为参数传递：

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```
-- The last expression, for example, denotes the function that takes
-- three types, {leanRef}`α`, {leanRef}`β`, and {leanRef}`γ`, and two functions, {leanRef}`g : β → γ`
-- and {leanRef}`f : α → β`, and returns the composition of {leanRef}`g` and {leanRef}`f`.
-- (Making sense of the type of this function requires an understanding
-- of _dependent products_, which will be explained below.)

例如，最后一个表达式表示一个函数，它接受
三个类型 {leanRef}`α`、{leanRef}`β` 和 {leanRef}`γ`，以及两个函数 {leanRef}`g : β → γ`
和 {leanRef}`f : α → β`，并返回 {leanRef}`g` 和 {leanRef}`f` 的复合。
（要理解这个函数的类型，需要理解 _依值积_，下面将对此进行解释。）

:::setup
```
variable (α : Type) (t : β)
-- Avoid warnings
axiom whatever : α
def b : γ := whatever
```

-- The general form of a lambda expression is {lean}`fun (x : α) => t`, where
-- the variable {leanRef}`x` is a “bound variable”: it is really a placeholder,
-- whose “scope” does not extend beyond the expression {leanRef}`t`.  For
-- example, the variable {lit}`b` in the expression {lean}`fun (b : β) (x : α) => b`
-- has nothing to do with the constant {lean}`b` declared earlier.  In fact,
-- the expression denotes the same function as {lean}`fun (u : β) (z : α) => u`.

lambda 表达式的一般形式是 {lean}`fun (x : α) => t`，其中
变量 {leanRef}`x` 是一个“绑定变量”：它实际上是一个占位符，
其“作用域”不会超出表达式 {leanRef}`t`。例如，
表达式 {lean}`fun (b : β) (x : α) => b` 中的变量 {lit}`b`
与前面声明的常量 {lean}`b` 没有任何关系。事实上，
该表达式表示的函数与 {lean}`fun (u : β) (z : α) => u` 相同。


-- Formally, expressions that are the same up to a renaming of bound
-- variables are called _alpha equivalent_, and are considered “the
-- same.” Lean recognizes this equivalence.
:::

形式上，除了绑定变量的重命名之外都相同的表达式被称为 _alpha 等价_，并且被认为是“相同的”。Lean 识别这种等价性。
:::

:::setup
```
variable (t : α → β) (s : α)
```
-- Notice that applying a term {lean}`t : α → β` to a term {lean}`s : α` yields
-- an expression {lean}`t s : β`. Returning to the previous example and
-- renaming bound variables for clarity, notice the types of the
-- following expressions:
:::

注意，将项 {lean}`t : α → β` 应用于项 {lean}`s : α` 会产生
表达式 {lean}`t s : β`。回到前面的例子，
为了清晰起见重命名绑定变量，请注意以下表达式的类型：
:::

```lean
#check (fun x : Nat => x) 1     -- (fun x => x) 1 : Nat
#check (fun x : Nat => true) 1  -- (fun x => true) 1 : Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
```

-- As expected, the expression {lean}`(fun x : Nat =>  x) 1` has type {lean}`Nat`.
-- In fact, more should be true: applying the expression {lean}`(fun x : Nat => x)` to
-- {lean}`1` should “return” the value {lean}`1`. And, indeed, it does:

正如预期的那样，表达式 {lean}`(fun x : Nat =>  x) 1` 具有类型 {lean}`Nat`。
事实上，更进一步：将表达式 {lean}`(fun x : Nat => x)` 应用于
{lean}`1` 应该“返回”值 {lean}`1`。确实如此：

```lean
#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
```

-- You will see later how these terms are evaluated. For now, notice that
-- this is an important feature of dependent type theory: every term has
-- a computational behavior, and supports a notion of _normalization_. In
-- principle, two terms that reduce to the same value are called
-- _definitionally equal_. They are considered “the same” by Lean's type
-- checker, and Lean does its best to recognize and support these
-- identifications.

稍后你将看到这些项是如何求值的。现在，请注意
这是依值类型论的一个重要特征：每个项都有
计算行为，并支持 _规范化_ 的概念。原则上，
归约为相同值的两个项被称为 _定义相等_。它们被 Lean 的类型检查器认为是“相同的”，
并且 Lean 尽最大努力识别和支持这些标识。

-- Lean is a complete programming language. It has a compiler that
-- generates a binary executable and an interactive interpreter. You can
-- use the command {kw}`#eval` to execute expressions, and it is the
-- preferred way of testing your functions.

Lean 是一门完整的编程语言。它有一个编译器，可以
生成二进制可执行文件和一个交互式解释器。你可以
使用命令 {kw}`#eval` 来执行表达式，这是
测试函数的首选方法。

:::comment
```
<!--
Note that `#eval` and
`#reduce` are _not_ equivalent. The command `#eval` first compiles
Lean expressions into an intermediate representation (IR) and then
uses an interpreter to execute the generated IR. Some builtin types
(e.g., `Nat`, `String`, `Array`) have a more efficient representation
in the IR. The IR has support for using foreign functions that are
opaque to Lean.

In contrast, the ``#reduce`` command relies on a reduction engine
similar to the one used in Lean's trusted kernel, the part of Lean
that is responsible for checking and verifying the correctness of
expressions and proofs. It is less efficient than ``#eval``, and
treats all foreign functions as opaque constants. You will learn later
that there are some other differences between the two commands.
-->
```
:::

-- # Definitions
# 定义
%%%
tag := "definitions"
%%%

-- Recall that the {kw}`def` keyword provides one important way of declaring new named
-- objects.

回想一下，{kw}`def` 关键字提供了声明新命名对象的一种重要方式。

```lean
def double (x : Nat) : Nat :=
  x + x
```

-- This might look more familiar to you if you know how functions work in
-- other programming languages. The name {leanRef}`double` is defined as a
-- function that takes an input parameter {leanRef}`x` of type {lean}`Nat`, where the
-- result of the call is {leanRef}`x + x`, so it is returning type {lean}`Nat`. You
-- can then invoke this function using:

如果你知道函数在其他编程语言中是如何工作的，这看起来可能会更熟悉。
名称 {leanRef}`double` 被定义为一个函数，它接受一个类型为 {lean}`Nat` 的输入参数 {leanRef}`x`，
调用的结果是 {leanRef}`x + x`，所以它返回类型 {lean}`Nat`。
然后你可以使用以下方式调用此函数：

```lean
def double (x : Nat) : Nat :=
 x + x
-----
#eval double 3    -- 6
```

-- In this case you can think of {kw}`def` as a kind of named {kw}`fun`.
-- The following yields the same result:

在这种情况下，你可以将 {kw}`def` 视为一种命名的 {kw}`fun`。
以下产生相同的结果：

```lean
def double : Nat → Nat :=
  fun x => x + x

#eval double 3    -- 6
```

-- You can omit the type declarations when Lean has enough information to
-- infer it.  Type inference is an important part of Lean:

当 Lean 有足够的信息来推断类型时，你可以省略类型声明。
类型推断是 Lean 的重要组成部分：

```lean
def double :=
  fun (x : Nat) => x + x
```

-- The general form of a definition is {lit}`def foo : α := bar` where
-- {lit}`α` is the type returned from the expression {lit}`bar`.  Lean can
-- usually infer the type {lit}`α`, but it is often a good idea to write it
-- explicitly.  This clarifies your intention, and Lean will flag an
-- error if the right-hand side of the definition does not have a matching
-- type.

定义的一般形式是 {lit}`def foo : α := bar`，其中
{lit}`α` 是表达式 {lit}`bar` 返回的类型。Lean 通常可以
推断类型 {lit}`α`，但显式写出它通常是一个好主意。
这阐明了你的意图，如果定义的右侧没有匹配的类型，Lean 将标记错误。

-- The right hand side {lit}`bar` can be any expression, not just a lambda.
-- So {kw}`def` can also be used to simply name a value like this:

右侧 {lit}`bar` 可以是任何表达式，不仅仅是 lambda。
所以 {kw}`def` 也可以用来简单地命名一个值，如下所示：

```lean
def pi := 3.141592654
```

-- {kw}`def` can take multiple input parameters.  Let's create one
-- that adds two natural numbers:

{kw}`def` 可以接受多个输入参数。让我们创建一个
将两个自然数相加的函数：

```lean
def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
```

-- The parameter list can be separated like this:

参数列表可以像这样分开：

```lean
def double (x : Nat) : Nat :=
  x + x
-----
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22
```

-- Notice here we called the {leanRef}`double` function to create the first
-- parameter to {leanRef}`add`.

注意这里我们调用了 {leanRef}`double` 函数来创建 {leanRef}`add` 的第一个参数。

-- You can use other more interesting expressions inside a {kw}`def`:

你可以在 {kw}`def` 中使用其他更有趣的表达式：

```lean
def greater (x y : Nat) :=
  if x > y then x
  else y
```

-- You can probably guess what this one will do.

你大概能猜到这个函数会做什么。

-- You can also define a function that takes another function as input.
-- The following calls a given function twice passing the output of the
-- first invocation to the second:

你也可以定义一个接受另一个函数作为输入的函数。
下面的代码调用给定的函数两次，将第一次调用的输出传递给第二次：

```lean
def double (x : Nat) : Nat :=
 x + x
-----
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8
```

-- Now to get a bit more abstract, you can also specify arguments that
-- are like type parameters:

现在稍微抽象一点，你也可以指定像类型参数一样的参数：

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

-- This means {leanRef}`compose` is a function that takes any two functions as input
-- arguments, so long as those functions each take only one input.
-- The type algebra {leanRef}`β → γ` and {leanRef}`α → β` means it is a requirement
-- that the type of the output of the second function must match the
-- type of the input to the first function—which makes sense, otherwise
-- the two functions would not be composable.

这意味着 {leanRef}`compose` 是一个接受任意两个函数作为输入参数的函数，
只要这些函数每个只接受一个输入。
类型代数 {leanRef}`β → γ` 和 {leanRef}`α → β` 意味着要求
第二个函数的输出类型必须与第一个函数的输入类型匹配——这是有道理的，否则
这两个函数将无法组合。

-- {leanRef}`compose` also takes a 3rd argument of type {leanRef}`α` which
-- it uses to invoke the second function (locally named {leanRef}`f`) and it
-- passes the result of that function (which is type {leanRef}`β`) as input to the
-- first function (locally named {leanRef}`g`).  The first function returns a type
-- {leanRef}`γ` so that is also the return type of the {leanRef}`compose` function.

{leanRef}`compose` 还接受一个类型为 {leanRef}`α` 的第 3 个参数，
它使用该参数来调用第二个函数（局部命名为 {leanRef}`f`），并将
该函数的结果（类型为 {leanRef}`β`）作为输入传递给
第一个函数（局部命名为 {leanRef}`g`）。第一个函数返回类型
{leanRef}`γ`，所以这也是 {leanRef}`compose` 函数的返回类型。

-- {leanRef}`compose` is also very general in that it works over any type
-- {leanRef}`α β γ`.  This means {leanRef}`compose` can compose just about any 2 functions
-- so long as they each take one parameter, and so long as the type of
-- output of the second matches the input of the first.  For example:

{leanRef}`compose` 也非常通用，因为它适用于任何类型
{leanRef}`α β γ`。这意味着 {leanRef}`compose` 几乎可以组合任何 2 个函数，
只要它们每个都接受一个参数，并且只要第二个函数的输出类型与第一个函数的输入类型匹配。例如：

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
def double (x : Nat) : Nat :=
  x + x
-----
def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3  -- 18
```

-- # Local Definitions
# 局部定义
%%%
tag := "local-definitions"
%%%

:::setup
```
variable (t1 : α) (t2 : β)
```

-- Lean also allows you to introduce “local” definitions using the
-- {kw}`let` keyword. The expression {lean}`let a := t1; t2` is
-- definitionally equal to the result of replacing every occurrence of
-- {leanRef}`a` in {leanRef}`t2` by {leanRef}`t1`.
:::

Lean 还允许你使用 {kw}`let` 关键字引入“局部”定义。
表达式 {lean}`let a := t1; t2` 在定义上等于
将 {leanRef}`t2` 中出现的每个 {leanRef}`a` 替换为 {leanRef}`t1` 的结果。
:::

```lean
#check let y := 2 + 2; y * y   -- let y := 2 + 2; y * y : Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16
```

:::setup
```
def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

variable (x : Nat)
```

-- Here, {lean}`twice_double x` is definitionally equal to the term {lean}`(x + x) * (x + x)`.

这里，{lean}`twice_double x` 在定义上等于项 {lean}`(x + x) * (x + x)`。

:::

-- You can combine multiple assignments by chaining {kw}`let` statements:

你可以通过链接 {kw}`let` 语句来组合多个赋值：

```lean
#check let y := 2 + 2; let z := y + y; z * z
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
```

-- The {lit}`;` can be omitted when a line break is used.
当使用换行符时，可以省略 {lit}`;`。
```lean
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
```

::::leanFirst
:::setup
```
variable (t1 : α) (t2 : β)
```

-- Notice that the meaning of the expression {lean}`let a := t1; t2` is very
-- similar to the meaning of {lean}`(fun a => t2) t1`, but the two are not
-- the same. In the first expression, you should think of every instance
-- of {leanRef (in:="let a := t1; t2")}`a` in {leanRef (in:="let a := t1; t2")}`t2` as a syntactic abbreviation for {leanRef (in:="let a := t1; t2")}`t1`. In the
-- second expression, {leanRef (in:="(fun a => t2) t1")}`a` is a variable, and the expression
-- {leanRef (in:="(fun a => t2) t1")}`fun a => t2` has to make sense independently of the value of {leanRef (in:="(fun a => t2) t1")}`a`.
-- The {kw}`let` construct is a stronger means of abbreviation, and there
-- are expressions of the form {lean}`let a := t1; t2` that cannot be
-- expressed as {lean}`(fun a => t2) t1`. As an exercise, try to understand
-- why the definition of {leanRef}`foo` below type checks, but the definition of
-- {lit}`bar` does not.
:::

注意，表达式 {lean}`let a := t1; t2` 的含义与 {lean}`(fun a => t2) t1` 的含义非常相似，但两者并不相同。
在第一个表达式中，你应该将 {leanRef (in:="let a := t1; t2")}`t2` 中出现的每个 {leanRef (in:="let a := t1; t2")}`a` 视为 {leanRef (in:="let a := t1; t2")}`t1` 的语法缩写。
在第二个表达式中，{leanRef (in:="(fun a => t2) t1")}`a` 是一个变量，表达式 {leanRef (in:="(fun a => t2) t1")}`fun a => t2` 必须独立于 {leanRef (in:="(fun a => t2) t1")}`a` 的值而有意义。
{kw}`let` 构造是一种更强的缩写手段，有些形式为 {lean}`let a := t1; t2` 的表达式不能表示为 {lean}`(fun a => t2) t1`。
作为一个练习，试着理解为什么下面 {leanRef}`foo` 的定义可以通过类型检查，而 {lit}`bar` 的定义却不能。
:::

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```
::::

-- # Variables and Sections
# 变量和小节
%%%
tag := "variables-and-sections"
%%%

-- Consider the following three function definitions:
考虑下面这三个函数定义：

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```

-- Lean provides you with the {kw}`variable` command to make such
-- declarations look more compact:
Lean 提供 {kw}`variable` 指令来让这些声明变得紧凑：

```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
```
-- You can declare variables of any type, not just {lean}`Type` itself:
你可以声明任意类型的变量，不只是 {lean}`Type` 类型：
```lean
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
```
-- Printing them out shows that all three groups of definitions have
-- exactly the same effect.
输出结果表明所有三组定义具有完全相同的效果。

-- The {kw}`variable` command instructs Lean to insert the declared
-- variables as bound variables in definitions that refer to them by
-- name. Lean is smart enough to figure out which variables are used
-- explicitly or implicitly in a definition. You can therefore proceed as
-- though {leanRef}`α`, {leanRef}`β`, {leanRef}`γ`, {leanRef}`g`, {leanRef}`f`, {leanRef}`h`, and {leanRef}`x` are fixed
-- objects when you write your definitions, and let Lean abstract the
-- definitions for you automatically.
{kw}`variable` 命令指示 Lean 将声明的变量作为绑定变量插入定义中，这些定义通过名称引用它们。
Lean 足够聪明，它能找出定义中显式或隐式使用哪些变量。
因此在写定义时，你可以将 {leanRef}`α`、{leanRef}`β`、{leanRef}`γ`、{leanRef}`g`、{leanRef}`f`、{leanRef}`h` 和 {leanRef}`x` 视为固定的对象，
并让 Lean 自动抽象这些定义。

-- When declared in this way, a variable stays in scope until the end of
-- the file you are working on. Sometimes, however, it is useful to limit
-- the scope of a variable. For that purpose, Lean provides the notion of
-- a {kw}`section`:
当以这种方式声明时，变量将一直保持存在，直到所处理的文件结束。
然而，有时需要限制变量的作用范围。Lean 提供了小节标记 {kw}`section` 来实现这个目的：

```lean
section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful
```

-- When the section is closed, the variables go out of scope, and cannot
-- be referenced any more.
当一个小节结束后，变量不再发挥作用。

-- You do not have to indent the lines within a section. Nor do you have
-- to name a section, which is to say, you can use an anonymous
-- {kw}`section` / {kw}`end` pair. If you do name a section, however, you
-- have to close it using the same name. Sections can also be nested,
-- which allows you to declare new variables incrementally.
你不需要缩进一个小节中的行。你也不需要命名一个小节，也就是说，你可以使用一个匿名的
{kw}`section` / {kw}`end` 对。但是，如果你确实命名了一个小节，你必须使用相同的名字关闭它。
小节也可以嵌套，这允许你逐步增加声明新变量。

-- # Namespaces
# 命名空间
%%%
tag := "namespaces"
%%%

-- Lean provides you with the ability to group definitions into nested,
-- hierarchical _namespaces_:
Lean 可以让你把定义放进一个嵌套的、层次化的 _命名空间_（_namespaces_）里：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa
```

-- When you declare that you are working in the namespace {leanRef}`Foo`, every
-- identifier you declare has a full name with prefix “{lit}`Foo.`”. Within
-- the namespace, you can refer to identifiers by their shorter names,
-- but once you end the namespace, you have to use the longer names.
-- Unlike {kw}`section`, namespaces require a name. There is only one
-- anonymous namespace at the root level.
当你声明你在命名空间 {leanRef}`Foo` 中工作时，你声明的每个标识符都有一个前缀 “{lit}`Foo.`” 的全名。
在命名空间中，可以通过较短的名称引用标识符，但是关闭命名空间后，必须使用较长的名称。
与 {kw}`section` 不同，命名空间需要一个名称。只有一个匿名命名空间在根级别上。

-- The {leanRef}`open` command brings the shorter names into the current
-- context. Often, when you import a module, you will want to open one or
-- more of the namespaces it contains, to have access to the short
-- identifiers. But sometimes you will want to leave this information
-- protected by a fully qualified name, for example, when they conflict
-- with identifiers in another namespace you want to use. Thus namespaces
-- give you a way to manage names in your working environment.
{leanRef}`open` 命令使你可以在当前使用较短的名称。通常，当你导入一个模块时，
你会想打开它包含的一个或多个命名空间，以访问短标识符。
但是，有时你希望将这些信息保留在一个完全限定的名称中，例如，当它们与你想要使用的另一个命名空间中的标识符冲突时。
因此，命名空间为你提供了一种在工作环境中管理名称的方法。

-- For example, Lean groups definitions and theorems involving lists into
-- a namespace {lit}`List`.
例如，Lean 把和列表相关的定义和定理都放在了命名空间 {lit}`List` 之中。
```lean
#check List.nil
#check List.cons
#check List.map
```
:::leanFirst
-- The command {leanRef}`open List` allows you to use the shorter names:
命令 {leanRef}`open List` 允许你使用短一点的名字：
```lean
open List

#check nil
#check cons
#check map
```
:::
-- Like sections, namespaces can be nested:
像小节一样，命名空间也是可以嵌套的：
```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa
```
-- Namespaces that have been closed can later be reopened, even in another file:
关闭的命名空间可以之后重新打开，甚至是在另一个文件里：

```lean
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo
```

-- Like sections, nested namespaces have to be closed in the order they
-- are opened. Namespaces and sections serve different purposes:
-- namespaces organize data and sections declare variables for insertion
-- in definitions. Sections are also useful for delimiting the scope of
-- commands such as {kw}`set_option` and {kw}`open`.
与小节一样，嵌套的名称空间必须按照打开的顺序关闭。命名空间和小节有不同的用途：
命名空间组织数据，小节声明变量，以便在定义中插入。
小节对于分隔 {kw}`set_option` 和 {kw}`open` 等命令的范围也很有用。

-- In many respects, however, a {kw}`namespace`{lit}`  ...  `{kw}`end` block behaves the
-- same as a {kw}`section`{lit}`  ...  `{kw}`end` block. In particular, if you use the
-- {kw}`variable` command within a namespace, its scope is limited to the
-- namespace. Similarly, if you use an {kw}`open` command within a
-- namespace, its effects disappear when the namespace is closed.
然而，在许多方面，{kw}`namespace`{lit}`  ...  `{kw}`end` 结构块和 {kw}`section`{lit}`  ...  `{kw}`end` 表现出来的特征是一样的。
尤其是你在命名空间中使用 {kw}`variable` 命令时，它的作用范围被限制在命名空间里。
类似地，如果你在命名空间中使用 {kw}`open` 命令，它的效果在命名空间关闭后消失。

-- # What makes dependent type theory dependent?
# 依值类型论“依赖”着什么？
%%%
tag := "what-makes-dependent-type-theory-dependent"
%%%

:::setup
```
variable (α : Type) (n : Nat)
```

-- The short explanation is that types can depend on parameters. You
-- have already seen a nice example of this: the type {lean}`List α` depends
-- on the argument {lean}`α`, and this dependence is what distinguishes
-- {lean}`List Nat` and {lean}`List Bool`. For another example, consider the
-- type {lean}`Vector α n`, the type of vectors of elements of {lean}`α` of
-- length {lean}`n`.  This type depends on _two_ parameters: the type of the
-- elements in the vector ({lean}`α : Type`) and the length of the vector
-- {lean}`n : Nat`.
:::
简单地说，类型可以依赖于参数。你已经看到了一个很好的例子：类型 {lean}`List α` 依赖于
参数 {lean}`α`，而这种依赖性是区分 {lean}`List Nat` 和 {lean}`List Bool` 的关键。
另一个例子，考虑类型 {lean}`Vector α n`，即长度为 {lean}`n` 的 {lean}`α` 元素的向量类型。
这个类型取决于 _两个_ 参数：向量中元素的类型 ({lean}`α : Type`) 和向量的长度
{lean}`n : Nat`。
:::

::::setup
```
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as
variable (α : Type) (a : α) (as : List α)
```
:::leanFirst

-- Suppose you wish to write a function {leanRef}`cons` which inserts a new
-- element at the head of a list. What type should {leanRef}`cons` have? Such a
-- function is _polymorphic_: you expect the {leanRef}`cons` function for
-- {lean}`Nat`, {lean}`Bool`, or an arbitrary type {leanRef}`α` to behave the same way.
-- So it makes sense to take the type to be the first argument to
-- {leanRef}`cons`, so that for any type, {lean}`α`, {lean}`cons α` is the insertion
-- function for lists of type {lean}`α`. In other words, for every {lean}`α`,
-- {lean}`cons α` is the function that takes an element {lean}`a : α` and a list
-- {lean}`as : List α`, and returns a new list, so you have {lean}`cons α a as : List α`.
假设你希望编写一个函数 {leanRef}`cons`，它在列表的开头插入一个新
元素。{leanRef}`cons` 应该有什么类型？这样的
函数是 _多态的_（polymorphic）：你期望 {lean}`Nat`，{lean}`Bool` 或任意类型 {leanRef}`α` 的 {leanRef}`cons` 函数表现相同的方式。
因此，将类型作为 {leanRef}`cons` 的第一个参数是有意义的，
因此对于任何类型 {lean}`α`，{lean}`cons α` 是类型 {lean}`α` 列表的插入
函数。换句话说，对于每个 {lean}`α`，
{lean}`cons α` 是将元素 {lean}`a : α` 插入列表
{lean}`as : List α` 的函数，并返回一个新的列表，因此有 {lean}`cons α a as : List α`。

-- It is clear that {lean}`cons α` should have type {lean}`α → List α → List α`.
-- But what type should {leanRef}`cons` have?  A first guess might be
-- {lean}`Type → α → List α → List α`, but, on reflection, this does not make
-- sense: the {leanRef}`α` in this expression does not refer to anything,
-- whereas it should refer to the argument of type {lean}`Type`.  In other
-- words, _assuming_ {lean}`α : Type` is the first argument to the function,
-- the type of the next two elements are {lean}`α` and {lean}`List α`. These
-- types vary depending on the first argument, {leanRef}`α`.
很明显，{lean}`cons α` 应该具有类型 {lean}`α → List α → List α`。
但是 {leanRef}`cons` 应该具有什么类型？初步猜测可能是
{lean}`Type → α → List α → List α`，但是仔细一想，这个类型表达式没有
意义：表达式中的 {leanRef}`α` 没有任何所指，
而它应该指的是类型为 {lean}`Type` 的参数。换句话说，
_假设_ {lean}`α : Type` 是函数的第一个参数，
接下来的两个元素的类型是 {lean}`α` 和 {lean}`List α`。这些
类型取决于第一个参数 {leanRef}`α`。

```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- cons Nat : Nat → List Nat → List Nat
#check cons Bool       -- cons Bool : Bool → List Bool → List Bool
#check cons            -- cons (α : Type) (a : α) (as : List α) : List α
```
:::
::::

:::setup
```
variable (α : Type) (β : α → Type) (a : α) (f : (a : α) → β a)
```

-- This is an instance of a _dependent function type_, or *dependent
-- arrow type*. Given {lean}`α : Type` and {lean}`β : α → Type`, think of {lean}`β`
-- as a family of types over {lean}`α`, that is, a type {lean}`β a` for each
-- {lean}`a : α`. In that case, the type {lean}`(a : α) → β a` denotes the type
-- of functions {lean}`f` with the property that, for each {lean}`a : α`, {lean}`f a`
-- is an element of {lean}`β a`. In other words, the type of the value
-- returned by {lean}`f` depends on its input.
:::
这就是 _依值函数类型_，或者 *依值箭头类型* 的一个例子。给定 {lean}`α : Type` 和 {lean}`β : α → Type`，把 {lean}`β`
考虑成 {lean}`α` 之上的类型族，也就是说，对于每个
{lean}`a : α` 都有类型 {lean}`β a`。在这种情况下，类型 {lean}`(a : α) → β a` 表示
具有如下性质的函数 {lean}`f` 的类型：对于每个 {lean}`a : α`，{lean}`f a`
是 {lean}`β a` 的一个元素。换句话说，{lean}`f` 返回值的类型
取决于其输入。
:::

:::setup
```
variable (α : Type) (β : Type) (a : α) (f : (a : α) → β a)
```
-- Notice that {lean}`(a : α) → β` makes sense for any expression {lean}`β : Type`.
-- When the value of {lean}`β` depends on {leanRef}`a` (as does, for
-- example, the expression {leanRef}`β a` in the previous paragraph),
-- {leanRef}`(a : α) → β` denotes a dependent function type. When {lean}`β` doesn't
-- depend on {leanRef}`a`, {leanRef}`(a : α) → β` is no different from the type
-- {lean}`α → β`.  Indeed, in dependent type theory (and in Lean), {lean}`α → β`
-- is just notation for {lean}`(a : α) → β` when {lean}`β` does not depend on {leanRef (in := "a : α")}`a`.
:::
注意，{lean}`(a : α) → β` 对于任意表达式 {lean}`β : Type` 都有意义。
当 {lean}`β` 的值依赖于 {leanRef}`a`（例如，在前一段的表达式 {leanRef}`β a`），
{leanRef}`(a : α) → β` 表示一个依值函数类型。当 {lean}`β` 不
依赖于 {leanRef}`a`，{leanRef}`(a : α) → β` 与类型
{lean}`α → β` 无异。实际上，在依值类型论（以及 Lean）中，{lean}`α → β`
表达的意思就是当 {lean}`β` 的值不依赖于 {leanRef (in := "a : α")}`a` 时的 {lean}`(a : α) → β`。
:::

-- Returning to the example of lists, you can use the command {kw}`#check` to
-- inspect the type of the following {lean}`List` functions.  The {lit}`@` symbol
-- and the difference between the round and curly braces will be
-- explained momentarily.
回到列表的例子，你可以使用命令 {kw}`#check` 来
检查下列 {lean}`List` 函数的类型。{lit}`@` 符号
以及圆括号和花括号之间的区别将在稍后解释。

```lean
#check @List.cons    -- @List.cons : {α : Type u_1} → α → List α → List α
#check @List.nil     -- @List.nil : {α : Type u_1} → List α
#check @List.length  -- @List.length : {α : Type u_1} → List α → Nat
#check @List.append  -- @List.append : {α : Type u_1} → List α → List α → List α
```

:::setup
```
variable (α : Type) (β : α → Type) (a : α) (b : β a)
```
-- Just as dependent function types {lean}`(a : α) → β a` generalize the
-- notion of a function type {leanRef}`α → β` by allowing {leanRef (in := "α → β")}`β` to depend on
-- {lean}`α`, dependent Cartesian product types {lean}`(a : α) × β a` generalize
-- the Cartesian product {lit}`α × β` in the same way. Dependent products
-- are also called _sigma_ types, and you can also write them as
-- {lean}`Σ a : α, β a`. You can use {lean (type := "(a : α) × β a")}`⟨a, b⟩` or {lean}`Sigma.mk a b` to create a
-- dependent pair.  The {lit}`⟨` and {lit}`⟩` characters may be typed with
-- {kbd}`\langle` and {kbd}`\rangle` or {kbd}`\<` and {kbd}`\>`, respectively.
:::
就像依值函数类型 {lean}`(a : α) → β a` 通过允许 {leanRef (in := "α → β")}`β` 依赖
{lean}`α` 从而推广了函数类型 {leanRef}`α → β`，依值笛卡尔积类型 {lean}`(a : α) × β a` 同样推广了
笛卡尔积 {lit}`α × β`。依值积
类型又称为 _sigma_ 类型，可写成
{lean}`Σ a : α, β a`。你可以用 {lean (type := "(a : α) × β a")}`⟨a, b⟩` 或者 {lean}`Sigma.mk a b` 来创建
依值对。{lit}`⟨` 和 {lit}`⟩` 符号可以用
{kbd}`\langle` 和 {kbd}`\rangle` 或者 {kbd}`\<` 和 {kbd}`\>` 来输入。
:::

```lean
universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5
```
-- The functions {leanRef}`f` and {leanRef}`g` above denote the same function.
上面的函数 {leanRef}`f` 和 {leanRef}`g` 表示相同的函数。


-- # Implicit Arguments
# 隐参数
%%%
tag := "implicit-arguments"
%%%

-- Suppose we have an implementation of lists as:
假设我们有一个列表的实现如下：

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
-----
#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α
```

-- Then, you can construct lists of {lean}`Nat` as follows:
然后，你可以建立一个 {lean}`Nat` 列表如下：

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
-----
#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs
```
:::setup
```
def Lst (α : Type u) : Type u := List α
variable (α : Type)
```
-- Because the constructors are polymorphic over types, we have to insert
-- the type {lean}`Nat` as an argument repeatedly. But this information is
-- redundant: one can infer the argument {leanRef}`α` in
-- {leanRef}`Lst.cons Nat 5 (Lst.nil Nat)` from the fact that the second argument, {leanRef}`5`, has
-- type {lean}`Nat`. One can similarly infer the argument in {leanRef}`Lst.nil Nat`, not
-- from anything else in that expression, but from the fact that it is
-- sent as an argument to the function {leanRef}`Lst.cons`, which expects an element
-- of type {lean}`Lst α` in that position.
:::
由于构造子对类型是多态的，我们需要重复插入
类型 {lean}`Nat` 作为一个参数。但是这个信息是
多余的：我们可以推断表达式 {leanRef}`Lst.cons Nat 5 (Lst.nil Nat)` 中参数 {leanRef}`α` 的类型，
这是通过第二个参数 {leanRef}`5` 的类型是 {lean}`Nat` 来实现的。类似地，我们可以推断 {leanRef}`Lst.nil Nat` 中参数的类型，
不是通过表达式中的其他任何东西，而是通过它作为函数 {leanRef}`Lst.cons` 的一个参数，
且这个函数在这个位置需要接收的是一个具有 {lean}`Lst α` 类型的参数来实现的。
:::

-- This is a central feature of dependent type theory: terms carry a lot
-- of information, and often some of that information can be inferred
-- from the context. In Lean, one uses an underscore, {lit}`_`, to specify
-- that the system should fill in the information automatically. This is
-- known as an “implicit argument.”
这是依值类型论的一个主要特征：项包含大量
信息，而且通常可以从上下文推断出一些信息。
在 Lean 中，我们使用下划线 {lit}`_` 来指定
系统应该自动填写信息。这就是所谓的“隐参数”。

```lean
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst
#check Lst.cons
#check Lst.nil
#check Lst.append
-----
#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs -- Lst.append Nat as bs : Lst Nat
```

-- It is still tedious, however, to type all these underscores. When a
-- function takes an argument that can generally be inferred from
-- context, Lean allows you to specify that this argument should, by
-- default, be left implicit. This is done by putting the arguments in
-- curly braces, as follows:
然而，敲这么多下划线仍然很繁琐。当一个
函数接受一个通常可以从上下文推断出来的参数时，
Lean 允许你指定该参数在默认情况下应该保持隐式。
这是通过将参数放入花括号来实现的，如下所示：

```lean
universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs
```

-- All that has changed are the braces around {leanRef}`α : Type u` in the
-- declaration of the variables. We can also use this device in function
-- definitions:
唯一改变的是变量声明中 {leanRef}`α : Type u` 周围的花括号。我们也可以在函数
定义中使用这个技巧：

```lean
universe u
def ident {α : Type u} (x : α) := x
```

-- Checking the type of {leanRef}`ident` requires wrapping it in parentheses to avoid having its signature shown:
检查 {leanRef}`ident` 的类型需要将其用括号括起来，以避免显示其签名：
```lean
universe u
def ident {α : Type u} (x : α) := x
---------
#check (ident)       -- ident : ?m.22 → ?m.22
#check ident 1       -- ident 1 : Nat
#check ident "hello" -- ident "hello" : String
#check @ident        -- @ident : {α : Type u_1} → α → α
```

-- The makes the first argument to {leanRef}`ident` implicit. Notationally,
-- this hides the specification of the type, making it look as though
-- {leanRef}`ident` simply takes an argument of any type. In fact, the function
-- {lean}`id` is defined in the standard library in exactly this way. We have
-- chosen a nontraditional name here only to avoid a clash of names.
这使得 {leanRef}`ident` 的第一个参数是隐式的。从符号上讲，
这隐藏了类型的说明，使它看起来好像
{leanRef}`ident` 只是接受任何类型的参数。事实上，函数
{lean}`id` 在标准库中就是以这种方式定义的。我们在这里
选择一个非传统的名字只是为了避免名字的冲突。

-- Variables can also be specified as implicit when they are declared with
-- the {kw}`variable` command:
{kw}`variable` 命令也可以用这种技巧来来把变量变成隐式的：

```lean
universe u

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident
#check ident 4
#check ident "hello"
```

-- This definition of {leanRef}`ident` here has the same effect as the one
-- above.
此处定义的 {leanRef}`ident` 和上面那个效果是一样的。

-- Lean has very complex mechanisms for instantiating implicit arguments,
-- and we will see that they can be used to infer function types,
-- predicates, and even proofs. The process of instantiating these
-- “holes,” or “placeholders,” in a term is often known as
-- _elaboration_. The presence of implicit arguments means that at times
-- there may be insufficient information to fix the meaning of an
-- expression precisely. An expression like {lean}`id` or {lean}`List.nil` is
-- said to be _polymorphic_, because it can take on different meanings in
-- different contexts.
Lean 有非常复杂的机制来实例化隐参数，
我们将看到它们可以用来推断函数类型、
谓词，甚至证明。实例化这些
“洞”或“占位符”的过程通常被称为
_繁饰（Elaboration）_。隐参数的存在意味着有时
可能没有足够的信息来精确地确定表达式的含义。
像 {lean}`id` 或 {lean}`List.nil` 这样的表达式被认为是 _多态的_，
因为它可以在不同的上下文中具有不同的含义。

:::setup
```
variable (T : Type) (e : T)
```

-- One can always specify the type {lean}`T` of an expression {lean}`e` by
-- writing {lean}`(e : T)`. This instructs Lean's elaborator to use the value
-- {lean}`T` as the type of {lean}`e` when trying to resolve implicit
-- arguments. In the second pair of examples below, this mechanism is
-- used to specify the desired types of the expressions {lean}`id` and
-- {lean}`List.nil`:
:::
可以通过写 {lean}`(e : T)` 来指定表达式 {lean}`e` 的类型 {lean}`T`。
这就指导 Lean 的繁饰器在试图解决隐式
参数时使用值 {lean}`T` 作为 {lean}`e` 的类型。
在下面的第二个例子中，这种机制用于
指定表达式 {lean}`id` 和 {lean}`List.nil` 所需的类型：

```lean
#check (List.nil)             -- [] : List ?m.2
#check (id)                   -- id : ?m.1 → ?m.1

#check (List.nil : List Nat)  -- [] : List Nat
#check (id : Nat → Nat)       -- id : Nat → Nat
```

-- Numerals are overloaded in Lean, but when the type of a numeral cannot
-- be inferred, Lean assumes, by default, that it is a natural number. So
-- the expressions in the first two {kw}`#check` commands below are
-- elaborated in the same way, whereas the third {kw}`#check` command
-- interprets {lean (type := "Int")}`2` as an integer.
Lean 中数字是重载的，但是当数字的类型不能
被推断时，Lean 默认假设它是一个自然数。因此，
下面的前两个 {kw}`#check` 命令中的表达式以同样的方式进行了
繁饰，而第三个 {kw}`#check` 命令
将 {lean (type := "Int")}`2` 解释为整数。

```lean
#check 2            -- 2 : Nat
#check (2 : Nat)    -- 2 : Nat
#check (2 : Int)    -- 2 : Int
```

:::setup
```
variable (foo : {α : Type} → α → β)
```

-- Sometimes, however, we may find ourselves in a situation where we have
-- declared an argument to a function to be implicit, but now want to
-- provide the argument explicitly. If {lean}`foo` is such a function, the
-- notation {lean}`@foo` denotes the same function with all the arguments
-- made explicit.
:::
然而，有时我们可能会发现自己处于这样一种情况：我们已经
声明了函数的参数是隐式的，但现在想
显式地提供参数。如果 {lean}`foo` 是有隐参数的函数，
符号 {lean}`@foo` 表示所有参数都是显式的该函数。

```lean
#check @id        -- @id : {α : Sort u_1} → α → α
#check @id Nat    -- id : Nat → Nat
#check @id Bool   -- id : Bool → Bool

#check @id Nat 1     -- id 1 : Nat
#check @id Bool true -- id true : Bool
```

-- Notice that now the first {kw}`#check` command gives the type of the
-- identifier, {leanRef}`id`, without inserting any placeholders. Moreover, the
-- output indicates that the first argument is implicit.
注意，现在第一个 {kw}`#check` 命令给出了
标识符 {leanRef}`id` 的类型，没有插入任何占位符。而且，
输出表明第一个参数是隐式的。
