import VersoManual
import TPiLZh.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiLZh

set_option linter.typography.dashes false

#doc (Manual) "归纳类型" =>
%%%
tag := "inductive-types"
file := "InductiveTypes"
%%%
-- Inductive Types

:::setup
```
variable {α : Sort u} {β : Sort v}
```


-- We have seen that Lean's formal foundation includes basic types,
-- {lean}`Prop`, {lean}`Type 0`, {lean}`Type 1`, {lean}`Type 2`, ..., and allows for the formation of
-- dependent function types, {lean}`(x : α) → β`. In the examples, we have
-- also made use of additional types like {lean}`Bool`, {lean}`Nat`, and {lean}`Int`,
-- and type constructors, like {lean}`List`, and product, {lit}`×`. In fact, in
-- Lean's library, every concrete type other than the universes and every
-- type constructor other than dependent arrows is an instance of a general family of
-- type constructions known as _inductive types_. It is remarkable that
-- it is possible to construct a substantial edifice of mathematics based
-- on nothing more than the type universes, dependent arrow types, and inductive
-- types; everything else follows from those.

我们已经看到 Lean 的形式基础包括基本类型，{lean}`Prop`、{lean}`Type 0`、{lean}`Type 1`、{lean}`Type 2` 等，
并允许形成依赖函数类型 {lean}`(x : α) → β`。在例子中，我们还使用了额外的类型，如 {lean}`Bool`、{lean}`Nat` 和 {lean}`Int`，
以及类型构造子，如 {lean}`List` 和乘积 {lit}`×`。事实上，在 Lean 的库中，除了宇宙之外的每一个具体类型和除了依赖箭头之外的每一个类型构造子都是一个被称为 _归纳类型_ 的类型构造的一般类别的实例。
值得注意的是，仅用类型宇宙、依赖箭头类型和归纳类型就可以构建一个内涵丰富的数学大厦；其他一切都源于这些。

:::

-- Intuitively, an inductive type is built up from a specified list of
-- constructors. In Lean, the syntax for specifying such a type is as
-- follows:

直观地说，一个归纳类型是由一个指定的构造子列表建立起来的。在 Lean 中，指定这种类型的语法如下：

:::setup
```
variable {α β ω : Type}

inductive Foo where
  | constructor₁ : α → Foo
  | constructor₂ : β → Foo
  | constructorₙ : ω → Foo

```

```
inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo
```

-- The intuition is that each constructor specifies a way of building new
-- objects of {lean}`Foo`, possibly from previously constructed values. The
-- type {lean}`Foo` consists of nothing more than the objects that are
-- constructed in this way.

我们的直觉是，每个构造子都指定了一种建立新的对象 {lean}`Foo` 的方法，可能是由以前构造的值构成。
{lean}`Foo` 类型只不过是由以这种方式构建的对象组成。



-- We will see below that the arguments of the constructors can include
-- objects of type {lean}`Foo`, subject to a certain “positivity” constraint,
-- which guarantees that elements of {lean}`Foo` are built from the bottom
-- up. Roughly speaking, each {lit}`...` can be any arrow type constructed from
-- {lean}`Foo` and previously defined types, in which {lean}`Foo` appears, if at
-- all, only as the “target” of the dependent arrow type.
:::

我们将在下面看到，构造子的参数可以包括 {lean}`Foo` 类型的对象，但要遵守一定的“正向性”约束，
即保证 {lean}`Foo` 的元素是自下而上构建的。粗略地说，每个 {lit}`...` 可以是由 {lean}`Foo` 和以前定义的类型构建的任何箭头类型，
其中 {lean}`Foo` 如果出现，也只是作为依赖箭头类型的“目标”。

-- We will provide a number of examples of inductive types. We will also
-- consider slight generalizations of the scheme above, to mutually
-- defined inductive types, and so-called _inductive families_.

我们将提供一些归纳类型的例子。我们还把上述方案稍微扩展，即相互定义的归纳类型，以及所谓的 _归纳族_。

-- As with the logical connectives, every inductive type comes with
-- introduction rules, which show how to construct an element of the
-- type, and elimination rules, which show how to “use” an element of the
-- type in another construction. The analogy to the logical connectives
-- should not come as a surprise; as we will see below, they, too, are
-- examples of inductive type constructions. You have already seen the
-- introduction rules for an inductive type: they are just the
-- constructors that are specified in the definition of the type. The
-- elimination rules provide for a principle of recursion on the type,
-- which includes, as a special case, a principle of induction as well.

就像逻辑连接词一样，每个归纳类型都有引入规则，说明如何构造该类型的一个元素；还有消去规则，说明如何在另一个构造中“使用”该类型的一个元素。
其实逻辑连接词也是归纳类型结构的例子。你已经看到了归纳类型的引入规则：它们只是在类型的定义中指定的构造子。
消去规则提供了类型上的递归原则，其中也包括作为一种特殊情况的归纳原则。

-- In the next chapter, we will describe Lean's function definition
-- package, which provides even more convenient ways to define functions
-- on inductive types and carry out inductive proofs. But because the
-- notion of an inductive type is so fundamental, we feel it is important
-- to start with a low-level, hands-on understanding. We will start with
-- some basic examples of inductive types, and work our way up to more
-- elaborate and complex examples.

在下一章中，我们将介绍 Lean 的函数定义包，它提供了更方便的方法来定义归纳类型上的函数并进行归纳证明。
但是由于归纳类型的概念是如此的基本，我们觉得从低级的、实践的理解开始是很重要的。
我们将从归纳类型的一些基本例子开始，然后逐步上升到更详细和复杂的例子。

-- # Enumerated Types
# 枚举类型
%%%
tag := "enumerated-types"
%%%

-- The simplest kind of inductive type is a type with a finite, enumerated list of elements.

最简单的归纳类型是一个具有有限的、可枚举的元素列表的类型。

```lean
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
```

-- The {kw}`inductive` command creates a new type, {leanRef}`Weekday`. The
-- constructors all live in the {lit}`Weekday` namespace.

{kw}`inductive` 命令创建了一个新类型 {leanRef}`Weekday`。构造子都在 {lit}`Weekday` 命名空间中。

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
------
#check Weekday.sunday

#check Weekday.monday

open Weekday

#check sunday

#check monday
```

-- You can omit {leanRef}`: Weekday` when declaring the {leanRef}`Weekday` inductive type.

在声明 {leanRef}`Weekday` 归纳类型时，可以省略 {leanRef}`: Weekday`。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

:::setup
```
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

-- Think of {leanRef}`sunday`, {leanRef}`monday`, ... , {leanRef}`saturday` as
-- being distinct elements of {leanRef}`Weekday`, with no other distinguishing
-- properties. The elimination principle, {name}`Weekday.rec`, is defined
-- along with the type {leanRef}`Weekday` and its constructors. It is also known
-- as a _recursor_, and it is what makes the type “inductive”: it allows
-- us to define a function on {leanRef}`Weekday` by assigning values
-- corresponding to each constructor. The intuition is that an inductive
-- type is exhaustively generated by the constructors, and has no
-- elements beyond those they construct.

把 {leanRef}`sunday`、{leanRef}`monday`、... 、{leanRef}`saturday` 看作是 {leanRef}`Weekday` 的不同元素，没有其他有区别的属性。
消去规则 {name}`Weekday.rec`，与 {leanRef}`Weekday` 类型及其构造子一起定义。它也被称为 *递归器（Recursor）*，
它是使该类型“归纳”的原因：它允许我们通过给每个构造子分配相应的值来定义 {leanRef}`Weekday` 的函数。
直观的说，归纳类型是由构造子详尽地生成的，除了它们构造的元素外，没有其他元素。

```signature
Weekday.rec.{u} {motive : Weekday → Sort u}
  (sunday : motive Weekday.sunday)
  (monday : motive Weekday.monday)
  (tuesday : motive Weekday.tuesday)
  (wednesday : motive Weekday.wednesday)
  (thursday : motive Weekday.thursday)
  (friday : motive Weekday.friday)
  (saturday : motive Weekday.saturday)
  (t : Weekday) :
  motive t
```

:::

:::leanFirst
-- We will use the {kw}`match` expression to define a function from {leanRef}`Weekday`
-- to the natural numbers:

我们将使用 {kw}`match` 表达式来定义一个从 {leanRef}`Weekday` 到自然数的函数：

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
------
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1

#eval numberOfDay Weekday.monday  -- 2

#eval numberOfDay Weekday.tuesday -- 3
```

-- When using Lean's logic, the {kw}`match` expression is compiled using the _recursor_ {leanRef}`Weekday.rec` generated when
-- you declare the inductive type. This ensures that the resulting term is well-defined in the type theory. For compiled code,
-- {kw}`match` is compiled as in other functional programming languages.
:::

在使用 Lean 的逻辑时，{kw}`match` 表达式是使用声明归纳类型时生成的 _递归器（recursor）_ {leanRef}`Weekday.rec` 来编译的。
这确保了结果项在类型论中是良定义的。对于编译后的代码，{kw}`match` 的编译方式与其他函数式编程语言相同。

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
------
open Weekday

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

set_option pp.all true
#print numberOfDay

#print numberOfDay.match_1

#print Weekday.casesOn

#check @Weekday.rec
```

:::leanFirst
-- When declaring an inductive datatype, you can use {leanRef}`deriving Repr` to instruct
-- Lean to generate a function that converts {leanRef}`Weekday` objects into text.
-- This function is used by the {kw}`#eval` command to display {leanRef}`Weekday` objects.
-- If no {lean}`Repr` exists, {kw}`#eval` attempts to derive one on the spot.

当声明一个归纳数据类型时，你可以使用 {leanRef}`deriving Repr` 来指示 Lean 生成一个函数，将 {leanRef}`Weekday` 对象转换为文本。
这个函数被 {kw}`#eval` 命令用来显示 {leanRef}`Weekday` 对象。如果不存在 {lean}`Repr`，{kw}`#eval` 会尝试当场派生一个。

```lean
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

open Weekday

#eval tuesday   -- Weekday.tuesday
```
:::

-- It is often useful to group definitions and theorems related to a
-- structure in a namespace with the same name. For example, we can put
-- the {leanRef}`numberOfDay` function in the {lit}`Weekday` namespace. We are
-- then allowed to use the shorter name when we open the namespace.

将与某一结构相关的定义和定理归入同名的命名空间通常很有用。例如，我们可以将 {leanRef}`numberOfDay` 函数放在 {lit}`Weekday` 命名空间中。
然后当我们打开命名空间时，我们就可以使用较短的名称。

:::leanFirst
-- We can define functions from {leanRef}`Weekday` to {leanRef}`Weekday`:

我们可以定义从 {leanRef}`Weekday` 到 {leanRef}`Weekday` 的函数：

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr
------
namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday

#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday
```
:::

:::leanFirst
-- How can we prove the general theorem that {leanRef}`next (previous d) = d`
-- for any Weekday {leanRef}`d`? You can use {kw}`match` to provide a proof of the claim for each
-- constructor:

我们如何证明对于任何 Weekday {leanRef}`d`，{leanRef}`next (previous d) = d` 的一般定理？
你可以使用 {kw}`match` 为每个构造子提供该主张的证明：

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr
namespace Weekday
def next (d : Weekday) : Weekday :=
 match d with
 | sunday    => monday
 | monday    => tuesday
 | tuesday   => wednesday
 | wednesday => thursday
 | thursday  => friday
 | friday    => saturday
 | saturday  => sunday
def previous (d : Weekday) : Weekday :=
 match d with
 | sunday    => saturday
 | monday    => sunday
 | tuesday   => monday
 | wednesday => tuesday
 | thursday  => wednesday
 | friday    => thursday
 | saturday  => friday
------
theorem next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl
```
:::

-- Using a tactic proof, we can be even more concise:

使用策略证明，我们可以更简洁：

```lean
inductive Weekday where
 | sunday : Weekday
 | monday : Weekday
 | tuesday : Weekday
 | wednesday : Weekday
 | thursday : Weekday
 | friday : Weekday
 | saturday : Weekday
 deriving Repr
namespace Weekday
def next (d : Weekday) : Weekday :=
 match d with
 | sunday    => monday
 | monday    => tuesday
 | tuesday   => wednesday
 | wednesday => thursday
 | thursday  => friday
 | friday    => saturday
 | saturday  => sunday
def previous (d : Weekday) : Weekday :=
 match d with
 | sunday    => saturday
 | monday    => sunday
 | tuesday   => monday
 | wednesday => tuesday
 | thursday  => wednesday
 | friday    => thursday
 | saturday  => friday
------
theorem next_previous (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl
```

-- {ref "tactics-for-inductive-types"}[Tactics for Inductive Types] below will introduce additional
-- tactics that are specifically designed to make use of inductive types.

下面的 {ref "tactics-for-inductive-types"}[归纳类型的策略] 将介绍专门设计用于利用归纳类型的其他策略。

-- Notice that, under the {tech}[propositions-as-types] correspondence, we can
-- use {kw}`match` to prove theorems as well as define functions.  In other
-- words, under the {tech}[propositions-as-types] correspondence, the proof by
-- cases is a kind of definition by cases, where what is being “defined”
-- is a proof instead of a piece of data.

注意，在 {tech}[命题即类型] 的对应关系下，我们可以使用 {kw}`match` 来证明定理以及定义函数。
换句话说，在 {tech}[命题即类型] 的对应关系下，按情况证明是一种按情况定义，其中被“定义”的是证明而不是数据。

-- The {lean}`Bool` type in the Lean library is an instance of
-- enumerated type.

Lean 库中的 {lean}`Bool` 类型是枚举类型的一个实例。

```lean
namespace Hidden
------
inductive Bool where
  | false : Bool
  | true  : Bool
------
end Hidden
```

-- (To run these examples, we put them in a namespace called {lit}`Hidden`,
-- so that a name like {leanRef}`Bool` does not conflict with the {lean}`Bool` in
-- the standard library. This is necessary because these types are part
-- of the Lean “prelude” that is automatically imported when the system
-- is started.)

（为了运行这些例子，我们将它们放在一个名为 {lit}`Hidden` 的命名空间中，这样像 {leanRef}`Bool` 这样的名字就不会与标准库中的 {lean}`Bool` 冲突。
这是必要的，因为这些类型是 Lean “prelude”的一部分，在系统启动时会自动导入。）


-- As an exercise, you should think about what the introduction and
-- elimination rules for these types do. As a further exercise, we
-- suggest defining boolean operations {lean}`and`, {lean}`or`, {lean}`not` on the
-- {leanRef}`Bool` type, and verifying common identities. Note that you can define a
-- binary operation like {leanRef}`and` using {kw}`match`:

作为一个练习，你应该思考这些类型的引入和消去规则是做什么的。作为进一步的练习，我们建议在 {leanRef}`Bool` 类型上定义布尔运算 {lean}`and`、{lean}`or`、{lean}`not`，
并验证常见的恒等式。注意，你可以使用 {kw}`match` 定义像 {leanRef}`and` 这样的二元运算：

```lean
namespace Hidden
------
def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false
-------
end Hidden
```

-- Similarly, most identities can be proved by introducing suitable {kw}`match`, and then using {lean}`rfl`.

同样，大多数恒等式可以通过引入合适的 {kw}`match`，然后使用 {lean}`rfl` 来证明。

-- # Constructors with Arguments
# 带参数的构造子
%%%
tag := "constructors-with-arguments"
%%%

:::setup
```
variable (α : Type u) (β : Type v) (a : α) (b : β)
```


-- Enumerated types are a very special case of inductive types, in which
-- the constructors take no arguments at all. In general, a
-- “construction” can depend on data, which is then represented in the
-- constructed argument. Consider the definitions of the product type and
-- sum type in the library:

枚举类型是归纳类型的一个非常特殊的情况，其中的构造子完全不接受参数。一般来说，一个“构造”可以依赖于数据，
然后这些数据在构造的参数中表示出来。考虑一下库中乘积类型和和类型的定义：

```lean
namespace Hidden
------
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
-------
end Hidden
```

-- Consider what is going on in these examples.
-- The product type has one constructor, {lean}`Prod.mk`,
-- which takes two arguments. To define a function on {leanRef}`Prod α β`, we
-- can assume the input is of the form {lean}`Prod.mk a b`, and we have to
-- specify the output, in terms of {leanRef}`a` and {leanRef}`b`. We can use this to
-- define the two projections for {leanRef}`Prod`. Remember that the standard
-- library defines notation {lean}`α × β` for {leanRef}`Prod α β` and {lean}`(a, b)` for
-- {lean}`Prod.mk a b`.

考虑一下这些例子中发生了什么。乘积类型有一个构造子 {lean}`Prod.mk`，它接受两个参数。
为了定义 {leanRef}`Prod α β` 上的函数，我们可以假设输入的形式是 {lean}`Prod.mk a b`，并且我们必须根据 {leanRef}`a` 和 {leanRef}`b` 指定输出。
我们可以用这个来定义 {leanRef}`Prod` 的两个投影。请记住，标准库为 {leanRef}`Prod α β` 定义了符号 {lean}`α × β`，
为 {lean}`Prod.mk a b` 定义了符号 {lean}`(a, b)`。

```lean
namespace Hidden
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β
------
def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b
--------
end Hidden
```

-- The function {leanRef}`fst` takes a pair, {leanRef}`p`. The {kw}`match` interprets
-- {leanRef}`p` as a pair, {leanRef}`Prod.mk a b`. Recall also from {ref "dependent-type-theory"}[Dependent Type Theory]
-- that to give these definitions the greatest generality possible, we allow
-- the types {leanRef}`α` and {leanRef}`β` to belong to any universe.

函数 {leanRef}`fst` 接受一个对子 {leanRef}`p`。{kw}`match` 将 {leanRef}`p` 解释为一个对子 {leanRef}`Prod.mk a b`。
还记得在 {ref "dependent-type-theory"}[依赖类型理论] 中，为了使这些定义尽可能通用，我们允许类型 {leanRef}`α` 和 {leanRef}`β` 属于任何宇宙。

:::
:::setup
```
universe u_2 u_3 u_1
variable (b : Bool) {α : Type u} {t1 t2 : α}
```

-- Here is another example where we use the recursor {lean (type := "{α : Type u_2} → {β : Type u_3} → {motive : α × β → Sort u_1} → (t : α × β) → ((fst : α) → (snd : β) → motive (fst, snd)) → motive t")}`Prod.casesOn` instead
-- of {kw}`match`.

这是另一个例子，我们使用递归器 {lean (type := "{α : Type u_2} → {β : Type u_3} → {motive : α × β → Sort u_1} → (t : α × β) → ((fst : α) → (snd : β) → motive (fst, snd)) → motive t")}`Prod.casesOn` 而不是 {kw}`match`。

```lean
def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p
    (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)

#eval prod_example (false, 3)
```

-- The argument {leanRef}`motive` is used to specify the type of the object you want to
-- construct, and it is a function because it may depend on the pair.
-- The {leanRef}`cond` function is a boolean conditional: {lean}`cond b t1 t2`
-- returns {lean}`t1` if {lean}`b` is true, and {lean}`t2` otherwise.
-- The function {leanRef}`prod_example` takes a pair consisting of a boolean,
-- {leanRef}`b`, and a number, {leanRef}`n`, and returns either {leanRef}`2 * n` or {leanRef}`2 * n + 1`
-- according to whether {leanRef}`b` is true or false.
:::

参数 {leanRef}`motive` 用于指定你想要构造的对象的类型，它是一个函数，因为它可能依赖于该对子。
{leanRef}`cond` 函数是一个布尔条件：如果 {lean}`b` 为真，{lean}`cond b t1 t2` 返回 {lean}`t1`，否则返回 {lean}`t2`。
函数 {leanRef}`prod_example` 接受一个由布尔值 {leanRef}`b` 和数字 {leanRef}`n` 组成的对子，
并根据 {leanRef}`b` 是真还是假返回 {leanRef}`2 * n` 或 {leanRef}`2 * n + 1`。

:::setup
```
open Sum
variable {α : Type u} {β : Type v} (a : α) (b : β)
```

-- In contrast, the sum type has _two_ constructors, {lean}`inl` and {lean}`inr`
-- (for “insert left” and “insert right”), each of which takes _one_
-- (explicit) argument. To define a function on {lean}`Sum α β`, we have to
-- handle two cases: either the input is of the form {lean}`inl a`, in which
-- case we have to specify an output value in terms of {leanRef}`a`, or the
-- input is of the form {lean}`inr b`, in which case we have to specify an
-- output value in terms of {leanRef}`b`.

相比之下，和类型有 _两个_ 构造子，{lean}`inl` 和 {lean}`inr`（代表“左插入”和“右插入”），每个构造子接受 _一个_（显式）参数。
为了定义 {lean}`Sum α β` 上的函数，我们必须处理两种情况：要么输入的形式是 {lean}`inl a`，在这种情况下我们必须根据 {leanRef}`a` 指定输出值；
要么输入的形式是 {lean}`inr b`，在这种情况下我们必须根据 {leanRef}`b` 指定输出值。

```lean
def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)

#eval sum_example (Sum.inr 3)
```

:::

:::setup
```
open Sum
variable (n : Nat)
```

-- This example is similar to the previous one, but now an input to
-- {leanRef}`sum_example` is implicitly either of the form {lean}`inl n` or {lean}`inr n`.
-- In the first case, the function returns {lean}`2 * n`, and the second
-- case, it returns {lean}`2 * n + 1`.

这个例子与前一个类似，但现在 {leanRef}`sum_example` 的输入隐式地要么是 {lean}`inl n` 的形式，要么是 {lean}`inr n` 的形式。
在第一种情况下，函数返回 {lean}`2 * n`，在第二种情况下，它返回 {lean}`2 * n + 1`。

:::

:::setup
```
variable {α β : Type} {a : α} {b : β}
open Sum
```


-- Notice that the product type depends on parameters {lean}`α β : Type`
-- which are arguments to the constructors as well as {lean}`Prod`. Lean
-- detects when these arguments can be inferred from later arguments to a
-- constructor or the return type, and makes them implicit in that case.

注意，乘积类型依赖于参数 {lean}`α β : Type`，它们既是构造子的参数，也是 {lean}`Prod` 的参数。
当这些参数可以从构造子的后续参数或返回类型中推断出来时，Lean 会检测到并将它们设为隐式。

-- In {ref "defining-the-natural-numbers"}[Defining the Natural Numbers]
-- we will see what happens when the
-- constructor of an inductive type takes arguments from the inductive
-- type itself. What characterizes the examples we consider in this
-- section is that each constructor relies only on previously specified types.

在 {ref "defining-the-natural-numbers"}[定义自然数] 中，我们将看到当归纳类型的构造子接受来自归纳类型本身的参数时会发生什么。
我们在本节中考虑的例子的特点是，每个构造子只依赖于先前指定的类型。

-- Notice that a type with multiple constructors is disjunctive: an
-- element of {lean}`Sum α β` is either of the form {lean}`inl a` _or_ of the
-- form {lean}`inl b`. A constructor with multiple arguments introduces
-- conjunctive information: from an element {lean}`Prod.mk a b` of
-- {lean}`Prod α β` we can extract {leanRef}`a` _and_ {leanRef}`b`. An arbitrary inductive type can
-- include both features, by having any number of constructors, each of
-- which takes any number of arguments.

注意，具有多个构造子的类型是析取的：{lean}`Sum α β` 的元素要么是 {lean}`inl a` 的形式，_要么_ 是 {lean}`inr b` 的形式。
具有多个参数的构造子引入了合取信息：从 {lean}`Prod α β` 的元素 {lean}`Prod.mk a b` 中，我们可以提取 {leanRef}`a` _和_ {leanRef}`b`。
任意归纳类型可以包含这两个特征，即拥有任意数量的构造子，每个构造子接受任意数量的参数。

:::

-- As with function definitions, Lean's inductive definition syntax will
-- let you put named arguments to the constructors before the colon:

与函数定义一样，Lean 的归纳定义语法允许你将构造子的命名参数放在冒号之前：

```lean
namespace Hidden
------
inductive Prod (α : Type u) (β : Type v) where
  | mk (fst : α) (snd : β) : Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β
-------
end Hidden
```

-- The results of these definitions are essentially the same as the ones given earlier in this section.

这些定义的结果本质上与本节前面给出的结果相同。

-- A type, like {leanRef}`Prod`, that has only one constructor is purely
-- conjunctive: the constructor simply packs the list of arguments into a
-- single piece of data, essentially a tuple where the type of subsequent
-- arguments can depend on the type of the initial argument. We can also
-- think of such a type as a “record” or a “structure”. In Lean, the
-- keyword {kw}`structure` can be used to define such an inductive type as
-- well as its projections, at the same time.

像 {leanRef}`Prod` 这样只有一个构造子的类型是纯合取的：构造子只是将参数列表打包成单个数据，本质上是一个元组，
其中后续参数的类型可以依赖于初始参数的类型。我们也可以把这种类型看作是“记录”或“结构”。
在 Lean 中，关键字 {kw}`structure` 可以用来同时定义这种归纳类型及其投影。

```lean
namespace Hidden
------
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
-------
end Hidden
```

-- This example simultaneously introduces the inductive type, {leanRef}`Prod`,
-- its constructor, {leanRef}`mk`, the usual eliminators ({lit}`rec` and
-- {lit}`recOn`), as well as the projections, {leanRef}`fst` and {leanRef}`snd`, as
-- defined above.

这个例子同时引入了归纳类型 {leanRef}`Prod`、它的构造子 {leanRef}`mk`、通常的消去器（{lit}`rec` 和 {lit}`recOn`），
以及如上定义的投影 {leanRef}`fst` 和 {leanRef}`snd`。

-- If you do not name the constructor, Lean uses {lit}`mk` as a default. For
-- example, the following defines a record to store a color as a triple
-- of RGB values:

如果你不命名构造子，Lean 默认使用 {lit}`mk`。例如，下面定义了一个记录，将颜色存储为 RGB 值的元组：

```lean
structure Color where
  red : Nat
  green : Nat
  blue : Nat
deriving Repr

def yellow := Color.mk 255 255 0

#eval Color.red yellow
```

-- The definition of {leanRef}`yellow` forms the record with the three values
-- shown, and the projection {leanRef}`Color.red` returns the red component.

{leanRef}`yellow` 的定义用显示的三个值形成了记录，投影 {leanRef}`Color.red` 返回红色分量。

-- The {kw}`structure` command is especially useful for defining algebraic
-- structures, and Lean provides substantial infrastructure to support
-- working with them. Here, for example, is the definition of a
-- semigroup:

{kw}`structure` 命令对于定义代数结构特别有用，Lean 提供了大量的基础设施来支持它们的使用。例如，这里是半群的定义：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
```

-- We will see more examples in the chapter on {ref "structures-and-records"}[structures and records].

我们将在 {ref "structures-and-records"}[结构体与记录] 一章中看到更多例子。

:::leanFirst
-- We have already discussed the dependent product type {leanRef}`Sigma`:

我们已经讨论了依赖乘积类型 {leanRef}`Sigma`：

```lean
namespace Hidden
------
inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β
-------
end Hidden
```
:::

-- Two more examples of inductive types in the library are the following:

库中还有两个归纳类型的例子：

```lean
namespace Hidden
------
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α
-------
end Hidden
```

:::setup
```
variable {α : Type u} {β : Type v} {γ : Type u'} (b : β) (f : α → Option β) (a : α)
```

-- In the semantics of dependent type theory, there is no built-in notion
-- of a partial function. Every element of a function type {lean}`α → β` or a
-- dependent function type {lean}`(a : α) → β` is assumed to have a value
-- at every input. The {lean}`Option` type provides a way of representing partial functions. An
-- element of {lean}`Option β` is either {lean}`none` or of the form {lean}`some b`,
-- for some value {lean}`b : β`. Thus we can think of an element {lean}`f` of the
-- type {lean}`α → Option β` as being a partial function from {lean}`α` to {lean}`β`:
-- for every {lean}`a : α`, {lean}`f a` either returns {lean (type := "Option β")}`none`, indicating
-- {lean}`f a` is “undefined”, or {lean}`some b`.

在依赖类型理论的语义中，没有内置的部分函数的概念。函数类型 {lean}`α → β` 或依赖函数类型 {lean}`(a : α) → β` 的每个元素都被假定在每个输入上都有值。
{lean}`Option` 类型提供了一种表示部分函数的方法。{lean}`Option β` 的元素要么是 {lean}`none`，要么是 {lean}`some b` 的形式，其中 {lean}`b : β`。
因此，我们可以把类型 {lean}`α → Option β` 的元素 {lean}`f` 看作是从 {lean}`α` 到 {lean}`β` 的部分函数：
对于每个 {lean}`a : α`，{lean}`f a` 要么返回 {lean (type := "Option β")}`none`（表示 {lean}`f a` “未定义”），要么返回 {lean}`some b`。

-- An element of {lean}`Inhabited α` is simply a witness to the fact that
-- there is an element of {lean}`α`. Later, we will see that {lean}`Inhabited` is
-- an example of a _type class_ in Lean: Lean can be instructed that
-- suitable base types are inhabited, and can automatically infer that
-- other constructed types are inhabited on that basis.

{lean}`Inhabited α` 的元素只是 {lean}`α` 中存在元素这一事实的见证。稍后，我们将看到 {lean}`Inhabited` 是 Lean 中 _类型类_ 的一个例子：
可以指示 Lean 适当的基本类型是居留的，并在此基础上自动推断其他构造类型也是居留的。

-- As exercises, we encourage you to develop a notion of composition for
-- partial functions from {lean}`α` to {lean}`β` and {lean}`β` to {lean}`γ`, and show
-- that it behaves as expected. We also encourage you to show that
-- {lean}`Bool` and {lean}`Nat` are inhabited, that the product of two inhabited
-- types is inhabited, and that the type of functions to an inhabited
-- type is inhabited.

作为练习，我们鼓励你开发从 {lean}`α` 到 {lean}`β` 以及从 {lean}`β` 到 {lean}`γ` 的部分函数的组合概念，并证明它的行为符合预期。
我们还鼓励你证明 {lean}`Bool` 和 {lean}`Nat` 是居留的，两个居留类型的乘积是居留的，以及到居留类型的函数的类型是居留的。

:::

-- # Inductively Defined Propositions
# 归纳定义的命题
%%%
tag := "inductively-defined-propositions"
%%%

-- Inductively defined types can live in any type universe, including the
-- bottom-most one, {lean}`Prop`. In fact, this is exactly how the logical
-- connectives are defined.

归纳定义的类型可以存在于任何类型宇宙中，包括最底层的 {lean}`Prop`。事实上，这正是逻辑连接词的定义方式。

```lean
namespace Hidden
------
inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b
-------
end Hidden
```

:::setup
```
variable (p : Prop) (hp : p) (α : Type u) (β : Type v)
```

-- You should think about how these give rise to the introduction and
-- elimination rules that you have already seen. There are rules that
-- govern what the eliminator of an inductive type can eliminate _to_,
-- that is, what kinds of types can be the target of a recursor. Roughly
-- speaking, what characterizes inductive types in {lean}`Prop` is that one
-- can only eliminate to other types in {lean}`Prop`. This is consistent with
-- the understanding that if {lean}`p : Prop`, an element {lean}`hp : p` carries
-- no data. There is a small exception to this rule, however, which we
-- will discuss below, in {ref "inductive-families"}[Inductive Families].

你应该思考这些是如何产生你已经看到的引入和消去规则的。有一些规则管理归纳类型的消去器可以消去 _到_ 什么，
也就是说，什么样的类型可以是递归器的目标。粗略地说，{lean}`Prop` 中归纳类型的特征是，人们只能消去到 {lean}`Prop` 中的其他类型。
这与如果 {lean}`p : Prop`，则元素 {lean}`hp : p` 不携带数据的理解是一致的。
然而，这个规则有一个小的例外，我们将在下面的 {ref "inductive-families"}[归纳族] 中讨论。


-- Even the existential quantifier is inductively defined:

甚至存在量词也是归纳定义的：

```lean
namespace Hidden
------
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
-------
end Hidden
```

-- Keep in mind that the notation {lean}`∃ x : α, p` is syntactic sugar for {lean}`Exists (fun x : α => p)`.

请记住，符号 {lean}`∃ x : α, p` 是 {lean}`Exists (fun x : α => p)` 的语法糖。


-- The definitions of {lean}`False`, {lean}`True`, {lean}`And`, and {lean}`Or` are
-- perfectly analogous to the definitions of {lean}`Empty`, {lean}`Unit`,
-- {lean}`Prod`, and {lean}`Sum`. The difference is that the first group yields
-- elements of {lean}`Prop`, and the second yields elements of {lean}`Type u` for
-- some {leanRef}`u`. In a similar way, {leanRef}`∃ x : α, p` is a {lean}`Prop`-valued
-- variant of {lean}`Σ x : α, β`.

{lean}`False`、{lean}`True`、{lean}`And` 和 {lean}`Or` 的定义与 {lean}`Empty`、{lean}`Unit`、
{lean}`Prod` 和 {lean}`Sum` 的定义完全类似。区别在于第一组产生 {lean}`Prop` 的元素，
而第二组产生某个 {leanRef}`u` 的 {lean}`Type u` 的元素。类似地，{leanRef}`∃ x : α, p` 是 {lean}`Σ x : α, β` 的 {lean}`Prop` 值变体。

:::

::::setup
```
variable (α : Type u) (β : Type v) (p : Prop)
```

-- This is a good place to mention another inductive type, denoted
-- {lean}`{x : α // p}`, which is sort of a hybrid between
-- {lean}`∃ x : α, p` and {lean}`Σ x : α, β`.

这里适合提及另一种归纳类型，记作 {lean}`{x : α // p}`，它是 {lean}`∃ x : α, p` 和 {lean}`Σ x : α, β` 的一种混合体。

```lean
namespace Hidden
------
inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p
-------
end Hidden
```
::::
::::setup
```
variable {α : Type u} {p : α → Prop}
```

:::leanFirst
-- In fact, in Lean, {leanRef}`Subtype` is defined using the structure command:

事实上，在 Lean 中，{leanRef}`Subtype` 是使用 structure 命令定义的：

```lean
namespace Hidden
------
structure Subtype {α : Sort u} (p : α → Prop) where
  val : α
  property : p val
-------
end Hidden
```


-- The notation {lean}`{x : α // p x}` is syntactic sugar for {lean}`Subtype (fun x : α => p x)`.
-- It is modeled after subset notation in set theory: the idea is that {leanRef}`{x : α // p x}`
-- denotes the collection of elements of {leanRef}`α` that have property {leanRef}`p`.

符号 {lean}`{x : α // p x}` 是 {lean}`Subtype (fun x : α => p x)` 的语法糖。
它模仿了集合论中的子集符号：其思想是 {leanRef}`{x : α // p x}` 表示 {leanRef}`α` 中具有属性 {leanRef}`p` 的元素集合。

:::
::::

-- # Defining the Natural Numbers
# 定义自然数
%%%
tag := "defining-the-natural-numbers"
%%%

-- The inductively defined types we have seen so far are “flat”:
-- constructors wrap data and insert it into a type, and the
-- corresponding recursor unpacks the data and acts on it. Things get
-- much more interesting when the constructors act on elements of the
-- very type being defined. A canonical example is the type {lean}`Nat` of
-- natural numbers:

到目前为止，我们所看到的归纳定义的类型都是“平坦的”：构造子打包数据并将其插入到一个类型中，而相应的递归器则解压数据并对其进行操作。
当构造子作用于被定义的类型中的元素时，事情就变得更加有趣了。一个典型的例子是自然数 {lean}`Nat` 类型：

namespace Hidden
------
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
-------
end Hidden

:::setup
open Nat
variable {motive : Nat → Sort u} {f : (n : Nat) → motive n} {n : Nat}

-- There are two constructors. We start with {lean}`zero : Nat`; it takes
-- no arguments, so we have it from the start. In contrast, the
-- constructor {lean}`succ` can only be applied to a previously constructed
-- {lean}`Nat`. Applying it to {lean}`zero` yields {lean}`succ zero : Nat`. Applying
-- it again yields {lean}`succ (succ zero) : Nat`, and so on. Intuitively,
-- {lean}`Nat` is the “smallest” type with these constructors, meaning that
-- it is exhaustively (and freely) generated by starting with {lean}`zero`
-- and applying {lean}`succ` repeatedly.

有两个构造子，我们从 {lean}`zero : Nat` 开始；它不需要参数，所以我们一开始就有了它。相反，构造子 {lean}`succ` 只能应用于先前构造的 {lean}`Nat`。
将其应用于 {lean}`zero`，得到 {lean}`succ zero : Nat`。再次应用它可以得到 {lean}`succ (succ zero) : Nat`，依此类推。
直观地说，{lean}`Nat` 是具有这些构造子的“最小”类型，这意味着它是通过从 {lean}`zero` 开始并重复应用 {lean}`succ` 这样无穷无尽地（并且自由地）生成的。


-- As before, the recursor for {lean}`Nat` is designed to define a dependent
-- function {lean}`f` from {lean}`Nat` to any domain, that is, an element {lean}`f`
-- of {lean}`(n : Nat) → motive n` for some {lean}`motive : Nat → Sort u`.
-- It has to handle two cases: the case where the input is {lean}`zero`, and the case where
-- the input is of the form {lean}`succ n` for some {lean}`n : Nat`. In the first
-- case, we simply specify a target value with the appropriate type, as
-- before. In the second case, however, the recursor can assume that a
-- value of {lean}`f` at {lean}`n` has already been computed. As a result, the
-- next argument to the recursor specifies a value for {lean}`f (succ n)` in
-- terms of {lean}`n` and {lean}`f n`. If we check the type of the recursor,
-- you find the following:

和以前一样，{lean}`Nat` 的递归器被设计用来定义一个从 {lean}`Nat` 到任何域的依赖函数 {lean}`f`，也就是一个 {lean}`(n : Nat) → motive n` 的元素 {lean}`f`，
其中 {lean}`motive : Nat → Sort u`。它必须处理两种情况：一种是输入为 {lean}`zero` 的情况，另一种是输入为 {lean}`succ n` 的情况，其中 {lean}`n : Nat`。
在第一种情况下，我们只需指定一个适当类型的目标值，就像以前一样。但是在第二种情况下，递归器可以假设在 {lean}`n` 处的 {lean}`f` 的值已经被计算过了。
因此，递归器的下一个参数是以 {lean}`n` 和 {lean}`f n` 来指定 {lean}`f (succ n)` 的值。如果检查递归器的类型，你会得到：

:::

```signature
Nat.rec.{u} :
  {motive : Nat → Sort u} →
  (zero : motive Nat.zero) →
  (succ : (n : Nat) → motive n → motive (Nat.succ n)) →
  (t : Nat) → motive t
```

-- The implicit argument, {leanRef}`motive`, is the codomain of the function being defined.
-- In type theory it is common to say {leanRef}`motive` is the _motive_ for the elimination/recursion,
-- since it describes the kind of object we wish to construct.
-- The next two arguments specify how to compute the zero and successor cases, as described above.
-- They are also known as the _minor premises_.
-- Finally, the {leanRef}`t : Nat` is the input to the function. It is also known as the _major premise_.

隐参数 {leanRef}`motive`，是被定义的函数的陪域。在类型论中，通常说 {leanRef}`motive` 是消去/递归的 _目的_ ，因为它描述了我们希望构建的对象类型。
接下来的两个参数指定了如何计算零和后继的情况，如上所述。它们也被称为 _小前提_。
最后，{leanRef}`t : Nat` 是函数的输入。它也被称为 _大前提_。

-- The {name}`Nat.recOn` is similar to {name}`Nat.rec` but the major premise occurs before the minor premises.

{name}`Nat.recOn` 与 {name}`Nat.rec` 类似，但大前提发生在小前提之前。

```signature
Nat.recOn.{u} :
  {motive : Nat → Sort u} →
  (t : Nat) →
  (zero : motive Nat.zero) →
  (succ : ((n : Nat) → motive n → motive (Nat.succ n))) →
  motive t
```

:::setup
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)
variable {n m : Nat}
open Nat

-- Consider, for example, the addition function {lean}`add m n` on the
-- natural numbers. Fixing {lean}`m`, we can define addition by recursion on
-- {lean}`n`. In the base case, we set {lean}`add m zero` to {lean}`m`. In the
-- successor step, assuming the value {lean}`add m n` is already determined,
-- we define {lean}`add m (succ n)` to be {lean}`succ (add m n)`.

例如，考虑自然数上的加法函数 {lean}`add m n`。固定 {lean}`m`，我们可以通过递归来定义 {lean}`n` 的加法。在基本情况下，我们将 {lean}`add m zero` 设为 {lean}`m`。
在后续步骤中，假设 {lean}`add m n` 的值已经确定，我们将 {lean}`add m (succ n)` 定义为 {lean}`succ (add m n)`。
:::

namespace Hidden
------
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

open Nat

#eval add (succ (succ zero)) (succ zero)
-------
end Hidden


-- It is useful to put such definitions into a namespace, {lean}`Nat`. We can
-- then go on to define familiar notation in that namespace. The two
-- defining equations for addition now hold definitionally:

将这些定义放入一个命名空间 {lean}`Nat` 是很有用的。然后我们可以继续在这个命名空间中定义熟悉的符号。现在加法的两个定义方程是定义上成立的：

namespace Hidden
inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr
------
namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

end Nat
-------
end Hidden

-- We will explain how the {kw}`instance` command works in
-- the {ref "type-classes"}[Type Classes] chapter. In the examples below, we will use
-- Lean's version of the natural numbers.

我们将在 {ref "type-classes"}[类型类] 一章中解释 {kw}`instance` 命令如何工作。在下面的例子中，我们将使用 Lean 自己的自然数版本。

::::leanFirst

:::setup
variable {n : Nat} {motive : Nat → Sort u} {ih : motive n}

-- Proving a fact like {lean}`0 + n = n`, however, requires a proof by induction.
-- As observed above, the induction principle is just a special case of the recursion principle,
-- when the codomain {lean}`motive n` is an element of {lean}`Prop`. It represents the familiar
-- pattern of an inductive proof: to prove {lean}`∀ n, motive n`, first prove {lean}`motive 0`,
-- and then, for arbitrary {lean}`n`, assume {lean}`ih : motive n` and prove {lean}`motive (n + 1)`.

然而，证明像 {lean}`0 + n = n` 这样的事实，需要用归纳法证明。如上所述，归纳原则只是递归原则的一个特例，其中陪域 {lean}`motive n` 是 {lean}`Prop` 的一个元素。
它代表了熟悉的归纳证明模式：要证明 {lean}`∀ n, motive n`，首先要证明 {lean}`motive 0`，然后对于任意的 {lean}`n`，假设 {lean}`ih : motive n` 并证明 {lean}`motive (n + 1)`。

namespace Hidden
------
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + (n + 1) = n + 1 from
    calc 0 + (n + 1)
      _ = (0 + n) + 1 := rfl
      _ = n + 1       := by rw [ih])
-------
end Hidden

:::
::::

-- Notice that, once again, when {name}`Nat.recOn` is used in the context of
-- a proof, it is really the induction principle in disguise. The
-- {tactic}`rw` and {tactic}`simp` tactics tend to be very effective in proofs
-- like these. In this case, each can be used to reduce the proof to:

请注意，当 {name}`Nat.recOn` 在证明中使用时，它实际上是变相的归纳原则。{tactic}`rw` 和 {tactic}`simp` 策略在这样的证明中往往非常有效。
在这种情况下，证明可以化简成：


namespace Hidden
------
open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [ih])
-------
end Hidden

:::setup
variable (m n k : Nat)

-- As another example, let us prove the associativity of addition,
-- {lean}`∀ m n k, m + n + k = m + (n + k)`.
-- (The notation {leanRef}`+`, as we have defined it, associates to the left, so {leanRef}`m + n + k` is really {lean}`(m + n) + k`.)
-- The hardest part is figuring out which variable to do the induction on. Since addition is defined by recursion on the second argument,
-- {leanRef (in := "n k,")}`k` is a good guess, and once we make that choice the proof almost writes itself:

另一个例子，让我们证明加法结合律，{lean}`∀ m n k, m + n + k = m + (n + k)`。
（我们定义的符号 {leanRef}`+` 是向左结合的，所以 {leanRef}`m + n + k` 实际上是 {lean}`(m + n) + k`。）
最难的部分是确定在哪个变量上做归纳。由于加法是由第二个参数的递归定义的，{leanRef (in := "n k,")}`k` 是一个很好的猜测，一旦我们做出这个选择，证明几乎是顺理成章的：
:::

namespace Hidden
------
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + (k + 1) = m + (n + (k + 1)) from
      calc m + n + (k + 1)
        _ = (m + n + k) + 1   := rfl
        _ = (m + (n + k)) + 1 := by rw [ih]
        _ = m + ((n + k) + 1) := rfl
        _ = m + (n + (k + 1)) := rfl)
-------
end Hidden

-- Once again, you can reduce the proof to:

你又可以化简证明：

```lean
open Nat
theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [add_succ (m + n) k, ih]; rfl)
```

-- Suppose we try to prove the commutativity of addition. Choosing induction on the second argument, we might begin as follows:

假设我们试图证明加法交换律。选择第二个参数做归纳法，我们可以这样开始：

```lean
open Nat
theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n
      _ = succ (m + n) := rfl
      _ = succ (n + m) := by rw [ih]
      _ = succ n + m   := sorry)
```

-- At this point, we see that we need another supporting fact, namely, that {leanRef}`succ (n + m)`{lit}`  =  `{leanRef}`succ n + m`.
-- You can prove this by induction on {leanRef}`m`:

在这一点上，我们看到我们需要另一个事实，即 {leanRef}`succ (n + m)`{lit}`  =  `{leanRef}`succ n + m`。
你可以通过对 {leanRef}`m` 的归纳来证明这一点：

```lean
open Nat

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    (show succ n + 0 = succ (n + 0) from rfl)
    (fun (m : Nat) (ih : succ n + m = succ (n + m)) =>
     show succ n + succ m = succ (n + succ m) from
     calc succ n + succ m
       _ = succ (succ n + m)   := rfl
       _ = succ (succ (n + m)) := by rw [ih]
       _ = succ (n + succ m)   := rfl)
```

-- You can then replace the {leanRef}`sorry` in the previous proof with {leanRef}`succ_add`. Yet again, the proofs can be compressed:

然后你可以用 {leanRef}`succ_add` 代替前面证明中的 {leanRef}`sorry`。然而，证明可以再次压缩：

```lean
namespace Hidden
inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

namespace Nat
theorem add_zero (m : Nat) : m + zero = m := rfl

theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl

theorem zero_add (n : Nat) : zero + n = n :=
  Nat.recOn (motive := fun x => zero + x = x) n
    rfl
    (fun n ih => by simpa [add_zero, add_succ])

end Nat
------
open Nat
theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simpa [add_succ (succ n)])

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
    (by simp [add_zero, zero_add])
    (fun m ih => by simp_all [succ_add, add_succ])
-------
end Hidden
```

-- # Other Recursive Data Types
# 其他递归数据类型
%%%
tag := "other-recursive-data-types"
%%%

:::leanFirst
-- Let us consider some more examples of inductively defined types. For
-- any type, {leanRef}`α`, the type {leanRef}`List α` of lists of elements of {leanRef}`α` is
-- defined in the library.

让我们考虑更多归纳定义类型的例子。对于任何类型 {leanRef}`α`，库中定义了 {leanRef}`α` 元素的列表类型 {leanRef}`List α`。

```lean
namespace Hidden
------
inductive List (α : Type u) where
  | nil  : List α
  | cons (h : α) (t : List α) : List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α) :
    append (cons a as) bs = cons a (append as bs) :=
  rfl

end List
-------
end Hidden
```

-- A list of elements of type {leanRef}`α` is either the empty list, {leanRef}`nil`, or
-- an element {leanRef}`h : α` followed by a list {leanRef}`t : List α`.
-- The first element, {leanRef}`h`, is commonly known as the “head” of the list,
-- and the remainder, {leanRef}`t`, is known as the “tail.”

{leanRef}`α` 类型的元素列表，要么是空列表 {leanRef}`nil`，要么是一个元素 {leanRef}`h : α`，后面是一个列表 {leanRef}`t : List α`。
第一个元素 {leanRef}`h`，通常被称为列表的“头”，剩余部分 {leanRef}`t`，被称为“尾”。
:::

-- As an exercise, prove the following:

作为一个练习，请证明以下内容：

```lean
namespace Hidden
inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α
namespace List
def append (as bs : List α) : List α :=
 match as with
 | nil       => bs
 | cons a as => cons a (append as bs)
theorem nil_append (as : List α) : append nil as = as :=
 rfl
theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
 rfl
------
theorem append_nil (as : List α) :
    append as nil = as :=
  sorry

theorem append_assoc (as bs cs : List α) :
    append (append as bs) cs = append as (append bs cs) :=
  sorry
-------
end List
end Hidden
```

:::setup
universe u
def length : {α : Type u} → List α → Nat := List.length
def append : {α : Type u} → List α → List α → List α := List.append
variable (as bs : List α)

-- Try also defining the function {lean}`length : {α : Type u} → List α → Nat` that returns the length of a list,
-- and prove that it behaves as expected (for example, {lean}`length (append as bs) = length as + length bs`).

还可以尝试定义函数 {lean}`length : {α : Type u} → List α → Nat`，返回一个列表的长度，并证明它的行为符合预期（例如，{lean}`length (append as bs) = length as + length bs`）。
:::

-- For another example, we can define the type of binary trees:

另一个例子，我们可以定义二叉树的类型：

```lean
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree
```

-- In fact, we can even define the type of countably branching trees:

事实上，我们甚至可以定义可数多叉树的类型：

```lean
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree
```

-- # Tactics for Inductive Types
# 归纳类型的策略
%%%
tag := "tactics-for-inductive-types"
%%%

-- Given the fundamental importance of inductive types in Lean, it should
-- not be surprising that there are a number of tactics designed to work
-- with them effectively. We describe some of them here.

归纳类型在 Lean 中有最根本的重要性，因此设计了一些方便使用的策略，这里讲几种。

:::setup
variable {x : InductiveType}

-- The {tactic}`cases` tactic works on elements of an inductively defined type,
-- and does what the name suggests: it decomposes the element according
-- to each of the possible constructors. In its most basic form, it is
-- applied to an element {lean}`x` in the local context. It then reduces the
-- goal to cases in which {lean}`x` is replaced by each of the constructions.

{tactic}`cases` 策略适用于归纳定义类型的元素，正如其名称所示：它根据每个可能的构造子分解元素。
在其最基本的形式中，它被应用于局部环境中的元素 {lean}`x`。然后，它将目标归约为 {lean}`x` 被每个构造子所取代的情况。
:::

```lean
example (p : Nat → Prop)
    (hz : p 0) (hs : ∀ n, p (Nat.succ n)) :
    ∀ n, p n := by
  intro n
  cases n
  . exact hz
--^ PROOF_STATE: A
  . apply hs
--^ PROOF_STATE: B
```

-- In the first branch, the proof state is:

在第一个分支中，证明状态是：

```proofState A
case zero
p : Nat → Prop
hz : p 0
hs : ∀ (n : Nat), p n.succ
⊢ p 0
```
-- In the second branch, it is:

在第二个分支中，它是：

```proofState B
case succ
p : Nat → Prop
hz : p 0
hs : ∀ (n : Nat), p n.succ
n✝ : Nat
⊢ p (n✝ + 1)
```

:::leanFirst
-- There are extra bells and whistles. For one thing, {leanRef}`cases` allows
-- you to choose the names for each alternative using a
-- {leanRef}`with` clause. In the next example, for example, we choose the name
-- {leanRef}`m` for the argument to {leanRef}`succ`, so that the second case refers to
-- {leanRef}`succ m`. More importantly, the cases tactic will detect any items
-- in the local context that depend on the target variable. It reverts
-- these elements, does the split, and reintroduces them. In the example
-- below, notice that the hypothesis {leanRef}`h : n ≠ 0` becomes {leanRef}`h : 0 ≠ 0`
-- in the first branch, and {leanRef}`h : m + 1 ≠ 0` in the second.

还有一些额外的修饰功能。首先，{leanRef}`cases` 允许你使用 {leanRef}`with` 子句来选择每个选项的名称。
例如在下一个例子中，我们为 {leanRef}`succ` 的参数选择 {leanRef}`m` 这个名字，这样第二个情况就指的是 {leanRef}`succ m`。
更重要的是，cases 策略将检测局部环境中任何依赖于目标变量的项目。它将这些元素还原，进行拆分，并重新引入它们。
在下面的例子中，注意假设 {leanRef}`h : n ≠ 0` 在第一个分支中变成 {leanRef}`h : 0 ≠ 0`，在第二个分支中变成 {leanRef}`h : m + 1 ≠ 0`。

```lean (showProofStates := "C D")
open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
  --     ^ PROOF_STATE: C
    apply absurd rfl h
  | succ m =>
  --       ^ PROOF_STATE: D
    rfl
```
:::

-- Notice that {leanRef}`cases` can be used to produce data as well as prove propositions.

注意 {leanRef}`cases` 可以用来产生数据，也可以用来证明命题。

```lean
def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl
```

-- Once again, cases will revert, split, and then reintroduce dependencies in the context.

再一次，cases 将还原、拆分，然后在上下文中重新引入依赖关系。

```lean
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

def f {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f myTuple = 7 :=
  rfl
```

-- Here is an example of multiple constructors with arguments.

这是一个有多个带参数构造子的例子。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e
```

-- The alternatives for each constructor don't need to be solved
-- in the order the constructors were declared.

每个构造子的选项不需要按照构造子声明的顺序来解决。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
------
def silly (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b
```

:::leanFirst
-- The syntax of the {leanRef}`with` is convenient for writing structured proofs.
-- Lean also provides a complementary {leanRef}`case` tactic, which allows you to focus on goal
-- assign variable names.

{leanRef}`with` 的语法对于编写结构化证明很方便。
Lean 还提供了一个补充的 {leanRef}`case` 策略，它允许你专注于目标并分配变量名。

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
------
def silly (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e
```
:::

-- The {leanRef}`case` tactic is clever, in that it will match the constructor to the appropriate goal. For example, we can fill the goals above in the opposite order:

{leanRef}`case` 策略很聪明，它会将构造子匹配到适当的目标。例如，我们可以按相反的顺序填充上面的目标：

```lean
inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo
------
def silly (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b
```

-- You can also use {leanRef}`cases` with an arbitrary expression. Assuming that
-- expression occurs in the goal, the cases tactic will generalize over
-- the expression, introduce the resulting universally quantified
-- variable, and case on that.

你也可以对任意表达式使用 {leanRef}`cases`。假设该表达式出现在目标中，cases 策略将对该表达式进行泛化，
引入结果的全称量化变量，并对其进行分情况讨论。

```lean
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  exact hz   -- goal is p 0
  apply hs   -- goal is a : Nat ⊢ p (succ a)
```

-- Think of this as saying “split on cases as to whether {leanRef}`m + 3 * k` is
-- zero or the successor of some number.” The result is functionally
-- equivalent to the following:

可以将其理解为“根据 {leanRef}`m + 3 * k` 是零还是某个数的后继来进行分情况讨论”。结果在功能上等同于以下内容：

```lean (showProofStates := "Z S")
open Nat

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  -- ^ PROOF_STATE: Z
  exact hz
  -- ^ PROOF_STATE: S
  apply hs
```

-- Notice that the expression {leanRef}`m + 3 * k` is erased by {leanRef}`generalize`; all
-- that matters is whether it is of the form {leanRef}`0` or {leanRef}`n✝ + 1`. This
-- form of {leanRef}`cases` will _not_ revert any hypotheses that also mention
-- the expression in the equation (in this case, {leanRef}`m + 3 * k`). If such a
-- term appears in a hypothesis and you want to generalize over that as
-- well, you need to {tactic}`revert` it explicitly.

注意，表达式 {leanRef}`m + 3 * k` 被 {leanRef}`generalize` 擦除了；重要的是它是否为 {leanRef}`0` 或 {leanRef}`n✝ + 1` 的形式。
这种形式的 {leanRef}`cases` _不会_ 还原任何也提到方程中表达式（在本例中为 {leanRef}`m + 3 * k`）的假设。
如果这样的项出现在假设中，并且你也想对其进行泛化，你需要显式地 {tactic}`revert` 它。

-- If the expression you case on does not appear in the goal, the
-- {tactic}`cases` tactic uses {tactic}`have` to put the type of the expression into
-- the context. Here is an example:

如果你进行分情况讨论的表达式没有出现在目标中，{tactic}`cases` 策略会使用 {tactic}`have` 将表达式的类型放入上下文中。
这是一个例子：

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  --           ^ PROOF_STATE: one
  case inr hge => exact h₂ hge
  --           ^ PROOF_STATE: two
```

-- The theorem {leanRef}`Nat.lt_or_ge m n` says {leanRef}`m < n`{lit}`  ∨  `{leanRef}`m ≥ n`, and it is
-- natural to think of the proof above as splitting on these two
-- cases. In the first branch, we have the hypothesis {leanRef}`hlt : m < n`, and
-- in the second we have the hypothesis {leanRef}`hge : m ≥ n`. The proof above
-- is functionally equivalent to the following:

定理 {leanRef}`Nat.lt_or_ge m n` 说 {leanRef}`m < n`{lit}`  ∨  `{leanRef}`m ≥ n`，很自然地可以将上面的证明看作是针对这两种情况进行拆分。
在第一个分支中，我们有假设 {leanRef}`hlt : m < n`，在第二个分支中，我们有假设 {leanRef}`hge : m ≥ n`。
上面的证明在功能上等同于以下内容：

```lean
example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge
```

-- After the first two lines, we have {leanRef}`h : m < n ∨ m ≥ n` as a
-- hypothesis, and we simply do cases on that.

在前两行之后，我们有 {leanRef}`h : m < n ∨ m ≥ n` 作为假设，我们只是对其进行分情况讨论。

:::leanFirst
-- Here is another example, where we use the decidability of equality on
-- the natural numbers to split on the cases {leanRef}`m = n` and {leanRef}`m ≠ n`.

这是另一个例子，我们利用自然数相等的可判定性来对 {leanRef}`m = n` 和 {leanRef}`m ≠ n` 的情况进行拆分。

```lean
#check Nat.sub_self

example (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne
```
:::

-- Remember that if you {kw}`open `{lit}`Classical`, you can use the law of the
-- excluded middle for any proposition at all. But using type class
-- inference (see {ref "type-classes"}[Type Classes]), Lean can actually
-- find the relevant decision procedure, which means that you can use the
-- case split in a computable function.

请记住，如果你 {kw}`open `{lit}`Classical`，你可以对任何命题使用排中律。
但是使用类型类推断（参见 {ref "type-classes"}[类型类]），Lean 实际上可以找到相关的判定过程，
这意味着你可以在可计算函数中使用情况拆分。

:::leanFirst
-- Just as the {leanRef}`cases` tactic can be used to carry out proof by cases,
-- the {leanRef}`induction` tactic can be used to carry out proofs by
-- induction. The syntax is similar to that of {leanRef}`cases`, except that the
-- argument can only be a term in the local context. Here is an example:

就像 {leanRef}`cases` 策略可以用来进行分情况证明一样，{leanRef}`induction` 策略可以用来进行归纳证明。
语法与 {leanRef}`cases` 类似，只是参数只能是局部上下文中的项。这是一个例子：

```lean
namespace Hidden
------
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
-------
end Hidden
```
:::

:::leanFirst
-- As with {leanRef}`cases`, we can use the {leanRef}`case` tactic instead of {leanRef}`with`.

与 {leanRef}`cases` 一样，我们可以使用 {leanRef}`case` 策略来代替 {leanRef}`with`。

```lean
namespace Hidden
------
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]
-------
end Hidden
```
:::

-- Here are some additional examples:

这里还有一些额外的例子：
:::TODO
FIXME
```lean
namespace Hidden
inductive Nat where
  | zero
  | succ : Nat → Nat

def Nat.toNat : Nat → _root_.Nat
  | .zero => .zero
  | .succ n => .succ n.toNat

def Nat.ofNat : _root_.Nat → Nat
  | .zero => .zero
  | .succ n => .succ (.ofNat n)

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add

instance : OfNat Nat n where
  ofNat := .ofNat n

@[simp]
theorem zero_zero : (.zero : Nat) = 0 := rfl
theorem add_zero (n : Nat) : n + 0 = n := rfl
theorem add_succ (n k : Nat) : n + k.succ = (n + k).succ := rfl
------
open Nat

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n <;> simp [*, add_zero, add_succ]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n <;> simp [*, add_zero, add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k <;> simp [*, add_zero, add_succ]
-------
end Hidden
```

-- The {leanRef}`induction` tactic also supports user-defined induction principles with
-- multiple targets (aka major premises). This example uses {name}`Nat.mod.inductionOn`, which has the following signature:

{leanRef}`induction` 策略还支持具有多个目标（即大前提）的用户定义归纳原则。
这个例子使用了 {name}`Nat.mod.inductionOn`，它具有以下签名：
:::
```signature
Nat.mod.inductionOn
  {motive : Nat → Nat → Sort u}
  (x y  : Nat)
  (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
  (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y) :
  motive x y
```


```lean
example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption
```

-- You can use the {kw}`match` notation in tactics too:

你也可以在策略中使用 {kw}`match` 符号：

```lean
example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2
```

:::leanFirst
-- As a convenience, pattern-matching has been integrated into tactics such as {leanRef}`intro` and {leanRef}`funext`.

为了方便起见，模式匹配已集成到诸如 {leanRef}`intro` 和 {leanRef}`funext` 之类的策略中。

```lean
example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (c, d)
  show a + d = d + a
  rw [Nat.add_comm]
```
:::

:::leanFirst
-- We close this section with one last tactic that is designed to
-- facilitate working with inductive types, namely, the {leanRef}`injection`
-- tactic. By design, the elements of an inductive type are freely
-- generated, which is to say, the constructors are injective and have
-- disjoint ranges. The {leanRef}`injection` tactic is designed to make use of
-- this fact:

我们用最后一个旨在促进归纳类型工作的策略来结束本节，即 {leanRef}`injection` 策略。
根据设计，归纳类型的元素是自由生成的，也就是说，构造子是单射的并且具有不相交的值域。
{leanRef}`injection` 策略旨在利用这一事实：

```lean
open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']
```
:::

-- The first instance of the tactic adds {leanRef}`h' : m.succ = n.succ`  to the
-- context, and the second adds {leanRef}`h'' : m = n`.

该策略的第一个实例将 {leanRef}`h' : m.succ = n.succ` 添加到上下文中，第二个实例添加 {leanRef}`h'' : m = n`。

-- The {leanRef}`injection` tactic also detects contradictions that arise when different constructors
-- are set equal to one another, and uses them to close the goal.

{leanRef}`injection` 策略还会检测当不同的构造子被设为相等时产生的矛盾，并使用它们来关闭目标。

```lean
open Nat

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction
```

-- As the second example shows, the {leanRef}`contradiction` tactic also detects contradictions of this form.

如第二个例子所示，{leanRef}`contradiction` 策略也会检测这种形式的矛盾。

-- # Inductive Families
# 归纳族
%%%
tag := "inductive-families"
%%%

-- We are almost done describing the full range of inductive definitions
-- accepted by Lean. So far, you have seen that Lean allows you to
-- introduce inductive types with any number of recursive
-- constructors. In fact, a single inductive definition can introduce an
-- indexed _family_ of inductive types, in a manner we now describe.

我们几乎已经描述完了 Lean 接受的所有归纳定义。到目前为止，你已经看到 Lean 允许你引入具有任意数量递归构造子的归纳类型。
事实上，单个归纳定义可以引入一个索引的归纳类型 _族_，我们现在将描述这种方式。

-- An inductive family is an indexed family of types defined by a
-- simultaneous induction of the following form:
归纳族是由以下形式的同时归纳定义的索引类型族：

```
inductive foo : ... → Sort u where
  | constructor₁ : ... → foo ...
  | constructor₂ : ... → foo ...
  ...
  | constructorₙ : ... → foo ...
```
::::setup
```
universe u
```

:::leanFirst
-- In contrast to an ordinary inductive definition, which constructs an
-- element of some {leanRef}`Sort u`, the more general version constructs a
-- function {lit}`... → `{lean}`Sort u`, where “{lit}`...`” denotes a sequence of
-- argument types, also known as _indices_. Each constructor then
-- constructs an element of some member of the family. One example is the
-- definition of {leanRef}`Vect α n`, the type of vectors of elements of {leanRef}`α`
-- of length {leanRef}`n`:
与普通的归纳定义不同，它构造了某个 {leanRef}`Sort u` 的元素，更一般的版本构造了一个函数 {lit}`... → `{lean}`Sort u`，其中 “{lit}`...`” 表示一串参数类型，也称为 _索引_ 。然后，每个构造子都会构造一个家族中某个成员的元素。一个例子是 {leanRef}`Vect α n` 的定义，它是长度为 {leanRef}`n` 的 {leanRef}`α` 元素的向量的类型：

```lean
inductive Vect (α : Type u) : Nat → Type u where
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
```
:::
::::

-- Notice that the {leanRef}`cons` constructor takes an element of
-- {leanRef}`Vect α n` and returns an element of {leanRef}`Vect α (n + 1)`, thereby using an
-- element of one member of the family to build an element of another.
注意，{leanRef}`cons` 构造子接收 {leanRef}`Vect α n` 的一个元素，并返回 {leanRef}`Vect α (n + 1)` 的一个元素，从而使用家族中的一个成员的元素来构建另一个成员的元素。

-- A more exotic example is given by the definition of the equality type in Lean:
一个更奇特的例子是由 Lean 中相等类型的定义：

```lean
namespace Hidden
------
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
-------
end Hidden
```

:::setup
```
variable (α : Sort u) (a : α) (x : α)
```

-- For each fixed {leanRef}`α : Sort u` and {leanRef}`a : α`, this definition
-- constructs a family of types {lean}`Eq a x`, indexed by {lean}`x : α`.
-- Notably, however, there is only one constructor, {leanRef}`refl`, which
-- is an element of {leanRef}`Eq a a`.
-- Intuitively, the only way to construct a proof of {lean}`Eq a x`
-- is to use reflexivity, in the case where {lean}`x` is {lean}`a`.
-- Note that {lean}`Eq a a` is the only inhabited type in the family of types
-- {lean}`Eq a x`. The elimination principle generated by Lean is as follows:

对于每个固定的 {leanRef}`α : Sort u` 和 {leanRef}`a : α`，这个定义构造了一个类型族 {lean}`Eq a x`，由 {lean}`x : α` 索引。
值得注意的是，只有一个构造子 {leanRef}`refl`，它是 {leanRef}`Eq a a` 的一个元素。
直观地说，构造 {lean}`Eq a x` 的证明的唯一方法是使用自反性，即在 {lean}`x` 为 {lean}`a` 的情况下。
请注意，{lean}`Eq a a` 是类型族 {lean}`Eq a x` 中唯一有居留元的类型。Lean 生成的消去原理如下：

:::

```lean
set_option pp.proofs true
--------
universe u v

#check (@Eq.rec : {α : Sort u} → {a : α} →
                  {motive : (x : α) → a = x → Sort v} →
                  motive a rfl →
                  {b : α} → (h : a = b) → motive b h)
```

-- It is a remarkable fact that all the basic axioms for equality follow
-- from the constructor, {leanRef}`refl`, and the eliminator, {leanRef}`Eq.rec`. The
-- definition of equality is atypical, however; see the discussion in {ref "axiomatic-details"}[Axiomatic Details].

-- The recursor {leanRef}`Eq.rec` is also used to define substitution:

一个显著的事实是，所有关于相等的基本公理都来自构造子 {leanRef}`refl` 和消去器 {leanRef}`Eq.rec`。
然而，相等的定义是不典型的，参见 {ref "axiomatic-details"}[公理化细节] 一节的讨论。

递归器 {leanRef}`Eq.rec` 也被用来定义代换：

```lean
namespace Hidden
------
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁
-------
end Hidden
```

-- You can also define {leanRef}`subst` using {kw}`match`.

你也可以使用 {kw}`match` 定义 {leanRef}`subst`。

```lean
namespace Hidden
------
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂
-------
end Hidden
```

-- Actually, Lean compiles the {kw}`match` expressions using a definition based on generated helpers
-- such as {name}`Eq.casesOn` and {name}`Eq.ndrec`, which are themselves defined using {leanRef}`Eq.rec`.

实际上，Lean 使用基于生成的辅助函数（如 {name}`Eq.casesOn` 和 {name}`Eq.ndrec`）的定义来编译 {kw}`match` 表达式，
而这些辅助函数本身是使用 {leanRef}`Eq.rec` 定义的。

```lean
namespace Hidden
------
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : a = b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂

set_option pp.all true
#print subst

#print subst.match_1_1

#print Eq.casesOn

#print Eq.ndrec
-------
end Hidden
```

-- Using the recursor or {kw}`match` with {leanRef}`h₁ : a = b`, we may assume {leanRef}`a` and {leanRef}`b` are the same,
-- in which case, {leanRef}`p b` and {leanRef}`p a` are the same.

使用递归器或 {kw}`match` 处理 {leanRef}`h₁ : a = b`，我们可以假设 {leanRef}`a` 和 {leanRef}`b` 是相同的，
在这种情况下，{leanRef}`p b` 和 {leanRef}`p a` 是相同的。

:::leanFirst
-- It is not hard to prove that {leanRef}`Eq` is symmetric and transitive.
-- In the following example, we prove {leanRef}`symm` and leave as exercises the theorems {leanRef}`trans` and {leanRef}`congr` (congruence).

证明 {leanRef}`Eq` 是对称的和传递的并不难。
在下面的例子中，我们证明 {leanRef}`symm`，并将定理 {leanRef}`trans` 和 {leanRef}`congr`（同余）留作练习。

```lean
namespace Hidden
------
variable {α β : Type u} {a b c : α}

theorem symm (h : Eq a b) : Eq b a :=
  match h with
  | rfl => rfl

theorem trans (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  sorry

theorem congr (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  sorry
-------
end Hidden
```
:::

-- In the type theory literature, there are further generalizations of
-- inductive definitions, for example, the principles of
-- _induction-recursion_ and _induction-induction_. These are not
-- supported by Lean.

在类型论文献中，有对归纳定义的进一步推广，例如，_归纳-递归（induction-recursion）_ 和 _归纳-归纳（induction-induction）_ 的原则。这些 Lean 并不支持。

-- # Axiomatic Details
# 公理化细节
%%%
tag := "axiomatic-details"
%%%

-- We have described inductive types and their syntax through
-- examples. This section provides additional information for those
-- interested in the axiomatic foundations.

我们已经通过例子描述了归纳类型和它们的语法。本节为那些对公理基础感兴趣的人提供额外的信息。

-- We have seen that the constructor to an inductive type takes
-- _parameters_—intuitively, the arguments that remain fixed
-- throughout the inductive construction—and _indices_, the arguments
-- parameterizing the family of types that is simultaneously under
-- construction. Each constructor should have a type, where the
-- argument types are built up from previously defined types, the
-- parameter and index types, and the inductive family currently being
-- defined. The requirement is that if the latter is present at all, it
-- occurs only _strictly positively_. This means simply that any argument
-- to the constructor in which it occurs is a dependent arrow type in which the
-- inductive type under definition occurs only as the resulting type,
-- where the indices are given in terms of constants and previous
-- arguments.

我们已经看到，归纳类型的构造子需要 _参量（parameters）_，即在整个归纳构造过程中保持固定的参数，和 _索引（indices）_，即参数化同时在构造中的类型族的参数。
每个构造子都应该有一个类型，其中的参数类型是由先前定义的类型、参量和索引类型以及当前正在定义的归纳族建立起来的。
要求是，如果后者存在，它只 _严格正向（strictly positively）_ 出现。
简单来说，这意味着它所出现的构造子的任何参数都是一个依赖箭头类型，其中定义中的归纳类型只作为结果类型出现，
其中的索引是以常量和先前的参数来给出。

-- Since an inductive type lives in {leanRef}`Sort u` for some {leanRef}`u`, it is
-- reasonable to ask _which_ universe levels {leanRef}`u` can be instantiated
-- to. Each constructor {lit}`c` in the definition of a family {lit}`C` of
-- inductive types is of the form

既然一个归纳类型对于某些 {leanRef}`u` 来说存在于 {leanRef}`Sort u` 中，那么我们有理由问 {leanRef}`u` 可以被实例化为 _哪些_ 宇宙层级。
归纳类型族 {lit}`C` 的定义中的每个构造子 {lit}`c` 的形式为

```
  c : (a : α) → (b : β[a]) → C a p[a,b]
```

-- where {lit}`a` is a sequence of data type parameters, {lit}`b` is the
-- sequence of arguments to the constructors, and {lit}`p[a, b]` are the
-- indices, which determine which element of the inductive family the
-- construction inhabits. (Note that this description is somewhat
-- misleading, in that the arguments to the constructor can appear in any
-- order as long as the dependencies make sense.) The constraints on the
-- universe level of {lit}`C` fall into two cases, depending on whether or
-- not the inductive type is specified to land in {lean}`Prop` (that is,
-- {lean}`Sort 0`).

其中 {lit}`a` 是一列数据类型的参量，{lit}`b` 是一列构造子的参数，{lit}`p[a, b]` 是索引，用于确定构造所处的归纳族的元素。
（请注意，这种描述有些误导，因为构造子的参数可以以任何顺序出现，只要依赖关系是合理的。）
对 {lit}`C` 的宇宙层级的约束分为两种情况，取决于归纳类型是否被指定落在 {lean}`Prop`（即 {lean}`Sort 0`）。

-- Let us first consider the case where the inductive type is _not_
-- specified to land in {lean}`Prop`. Then the universe level {leanRef}`u` is
-- constrained to satisfy the following:

我们首先考虑归纳类型 _不_ 指定落在 {lean}`Prop` 的情况。那么宇宙层级 {leanRef}`u` 被限制为满足以下条件：

-- > For each constructor {lit}`c` as above, and each {lit}`βk[a]` in the sequence {lit}`β[a]`, if {lit}`βk[a] : Sort v`, we have {leanRef}`u` ≥ {leanRef}`v`.

> 对于上面的每个构造子 {lit}`c`，以及序列 {lit}`β[a]` 中的每个 {lit}`βk[a]`，如果 {lit}`βk[a] : Sort v`，我们有 {leanRef}`u` ≥ {leanRef}`v`。

-- In other words, the universe level {leanRef}`u` is required to be at least as
-- large as the universe level of each type that represents an argument
-- to a constructor.

换句话说，宇宙层级 {leanRef}`u` 被要求至少与代表构造子参数的每个类型的宇宙层级一样大。

-- When the inductive type is specified to land in {lean}`Prop`, there are no
-- constraints on the universe levels of the constructor arguments. But
-- these universe levels do have a bearing on the elimination
-- rule. Generally speaking, for an inductive type in {lean}`Prop`, the
-- motive of the elimination rule is required to be in {lean}`Prop`.

当归纳类型被指定落在 {lean}`Prop` 中时，对构造子参数的宇宙层级没有任何限制。但是这些宇宙层级对消去规则有影响。
一般来说，对于 {lean}`Prop` 中的归纳类型，消去规则的 motive 被要求在 {lean}`Prop` 中。

-- There is an exception to this last rule: we are allowed to eliminate
-- from an inductively defined {lean}`Prop` to an arbitrary {leanRef}`Sort` when
-- there is only one constructor and each constructor argument is either
-- in {lean}`Prop` or an index. The intuition is that in this case the
-- elimination does not make use of any information that is not already
-- given by the mere fact that the type of argument is inhabited. This
-- special case is known as _singleton elimination_.

这最后一条规则有一个例外：当只有一个构造子，并且每个构造子参数都在 {lean}`Prop` 中或者是一个索引时，
我们可以从一个归纳定义的 {lean}`Prop` 消去到一个任意的 {leanRef}`Sort`。
直观地说，在这种情况下，消去并不利用任何信息，而这些信息并不是由参数类型有居留元这一简单的事实所提供的。
这种特殊情况被称为 _单子消去（singleton elimination）_。

-- We have already seen singleton elimination at play in applications of
-- {name}`Eq.rec`, the eliminator for the inductively defined equality
-- type. We can use an element {leanRef}`h : Eq a b` to cast an element
-- {leanRef}`h₂ : p a` to {leanRef}`p b` even when {leanRef}`p a` and {leanRef}`p b` are arbitrary types,
-- because the cast does not produce new data; it only reinterprets the
-- data we already have. Singleton elimination is also used with
-- heterogeneous equality and well-founded recursion, which will be
-- discussed in a the chapter on {ref "well-founded-recursion-and-induction"}[induction and recursion].

我们已经在 {name}`Eq.rec` 的应用中看到了单子消去的作用，这是归纳定义的相等类型的消去器。
我们可以使用一个元素 {leanRef}`h : Eq a b` 来将一个元素 {leanRef}`h₂ : p a` 转换为 {leanRef}`p b`，
即使 {leanRef}`p a` 和 {leanRef}`p b` 是任意类型，因为转换并不产生新的数据；它只是重新解释了我们已经有的数据。
单子消去也用于异质相等和良基递归，这将在 {ref "well-founded-recursion-and-induction"}[归纳和递归] 一章中讨论。

-- # Mutual and Nested Inductive Types
# 相互和嵌套的归纳类型
%%%
tag := "mutual-and-nested-inductive-types"
%%%

-- We now consider two generalizations of inductive types that are often
-- useful, which Lean supports by “compiling” them down to the more
-- primitive kinds of inductive types described above. In other words,
-- Lean parses the more general definitions, defines auxiliary inductive
-- types based on them, and then uses the auxiliary types to define the
-- ones we really want. Lean's equation compiler, described in the next
-- chapter, is needed to make use of these types
-- effectively. Nonetheless, it makes sense to describe the declarations
-- here, because they are straightforward variations on ordinary
-- inductive definitions.

我们现在考虑两个经常有用的归纳类型的推广，Lean 通过“编译”它们来支持上述更原始的归纳类型种类。
换句话说，Lean 解析了更一般的定义，在此基础上定义了辅助的归纳类型，然后使用辅助类型来定义我们真正想要的类型。
下一章将介绍 Lean 的方程编译器，它需要有效地利用这些类型。
尽管如此，在这里描述这些声明还是有意义的，因为它们是普通归纳定义的直接变形。

-- First, Lean supports _mutually defined_ inductive types. The idea is
-- that we can define two (or more) inductive types at the same time,
-- where each one refers to the other(s).

首先，Lean 支持 _相互定义（mutually defined）_ 的归纳类型。这个想法是，我们可以同时定义两个（或更多）归纳类型，其中每个类型都指代其他类型。

```lean
mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end
```

-- In this example, two types are defined simultaneously: a natural
-- number {leanRef}`n` is {leanRef}`Even` if it is {lean}`0` or one more than an {leanRef}`Odd`
-- number, and {leanRef}`Odd` if it is one more than an {leanRef}`Even` number.
-- In the exercises below, you are asked to spell out the details.

在这个例子中，同时定义了两种类型：一个自然数 {leanRef}`n` 如果是 {lean}`0` 或比 {leanRef}`Odd` 数多一个，就是 {leanRef}`Even`；
如果是比 {leanRef}`Even` 数多一个，就是 {leanRef}`Odd`。在下面的练习中，要求你写出细节。

:::leanFirst
-- A mutual inductive definition can also be used to define the notation
-- of a finite tree with nodes labelled by elements of {leanRef (in:="Tree (α")}`α`:

相互的归纳定义也可以用来定义有限树的表示法，节点由 {leanRef (in:="Tree (α")}`α` 的元素标记：

```lean
mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end
```
:::

-- With this definition, one can construct an element of {leanRef}`Tree α` by
-- giving an element of {leanRef}`α` together with a list of subtrees, possibly
-- empty. The list of subtrees is represented by the type {leanRef}`TreeList α`,
-- which is defined to be either the empty list, {leanRef}`nil`, or the
-- {leanRef}`cons` of a tree and an element of {leanRef}`TreeList α`.

有了这个定义，我们可以通过给出一个 {leanRef}`α` 的元素和一个子树列表（可能是空的）来构造 {leanRef}`Tree α` 的元素。
子树列表由 {leanRef}`TreeList α` 类型表示，它被定义为空列表 {leanRef}`nil`，或者是一棵树的 {leanRef}`cons` 和 {leanRef}`TreeList α` 的一个元素。

:::leanFirst
-- This definition is inconvenient to work with, however. It would be
-- much nicer if the list of subtrees were given by the type
-- {leanRef}`List (Tree α)`, especially since Lean's library contains a number of functions
-- and theorems for working with lists. One can show that the type
-- {leanRef}`TreeList α` is _isomorphic_ to {leanRef}`List (Tree α)`, but translating
-- results back and forth along this isomorphism is tedious.

然而，这个定义在工作中是不方便的。如果子树的列表是由 {leanRef}`List (Tree α)` 类型给出的，那就更好了，
尤其是 Lean 的库中包含了一些处理列表的函数和定理。
我们可以证明 {leanRef}`TreeList α` 类型与 {leanRef}`List (Tree α)` 是 _同构（isomorphic）_ 的，
但是沿着这个同构关系来回翻译结果是很乏味的。

-- In fact, Lean allows us to define the inductive type we really want:

事实上，Lean 允许我们定义我们真正想要的归纳类型：

```lean
inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α
```
:::

-- This is known as a _nested_ inductive type. It falls outside the
-- strict specification of an inductive type given in the last section
-- because {leanRef}`Tree` does not occur strictly positively among the
-- arguments to {leanRef}`mk`, but, rather, nested inside the {leanRef}`List` type
-- constructor. Lean then automatically builds the
-- isomorphism between {leanRef}`TreeList α` and {leanRef}`List (Tree α)` in its kernel,
-- and defines the constructors for {leanRef}`Tree` in terms of the isomorphism.

这就是所谓的 _嵌套（nested）_ 归纳类型。它不属于上一节给出的归纳类型的严格规范，
因为 {leanRef}`Tree` 不是严格正向地出现在 {leanRef}`mk` 的参数中，而是嵌套在 {leanRef}`List` 类型构造子中。
然后 Lean 在其内核中自动建立了 {leanRef}`TreeList α` 和 {leanRef}`List (Tree α)` 之间的同构关系，
并根据同构关系定义了 {leanRef}`Tree` 的构造子。

-- # Exercises
# 练习
%%%
tag := "inductive-types-exercises"
%%%

```setup
open Nat
variable {n m : Nat}
def length : List α → Nat
  | [] => 0
  | _ :: xs => length xs + 1
def reverse : List α → List α := go []
where
  go (acc : List α) : List α → List α
    | [] => acc
    | x :: xs => go (x :: acc) xs
variable {xs ys : List α}

inductive Term where
  | const (n : Nat)
  | var (n : Nat)
  | plus (s t : Term)
  | times (s t : Term)
open Term
variable {s t : Term}

```

-- 1. Try defining other operations on the natural numbers, such as
--    multiplication, the predecessor function (with {lean}`pred 0 = 0`),
--    truncated subtraction (with {lean}`n - m = 0` when {lean}`m` is greater
--    than or equal to {lean}`n`), and exponentiation. Then try proving some
--    of their basic properties, building on the theorems we have already
--    proved.

1. 尝试定义自然数的其他运算，如乘法、前继函数（定义 {lean}`pred 0 = 0`）、
   截断减法（当 {lean}`m` 大于或等于 {lean}`n` 时，{lean}`n - m = 0`）和乘方。
   然后在我们已经证明的定理的基础上，尝试证明它们的一些基本属性。

--    Since many of these are already defined in Lean's core library, you
--    should work within a namespace named {lit}`Hidden`, or something like
--    that, in order to avoid name clashes.

   由于其中许多已经在 Lean 的核心库中定义，你应该在一个名为 {lit}`Hidden` 或类似的命名空间中工作，以避免名称冲突。

-- 2. Define some operations on lists, like a {lean}`length` function or the
--    {lean}`reverse` function. Prove some properties, such as the following:

2. 定义一些对列表的操作，如 {lean}`length` 函数或 {lean}`reverse` 函数。证明一些属性，比如下面这些：

--    a. {lean}`length (xs ++ ys) = length xs + length ys`

   a. {lean}`length (xs ++ ys) = length xs + length ys`

--    b. {lean}`length (reverse xs) = length xs`

   b. {lean}`length (reverse xs) = length xs`

--    c. {lean}`reverse (reverse xs) = xs`

   c. {lean}`reverse (reverse xs) = xs`

-- 3. Define an inductive data type consisting of terms built up from the following constructors:

3. 定义一个归纳数据类型，由以下构造子建立的项组成：

--    - {lean}`const n`, a constant denoting the natural number {lean}`n`
--    - {lean}`var n`, a variable, numbered {lean}`n`
--    - {lean}`plus s t`, denoting the sum of {leanRef}`s` and {leanRef}`t`
--    - {lean}`times s t`, denoting the product of {leanRef}`s` and {leanRef}`t`

   - {lean}`const n`，一个表示自然数 {lean}`n` 的常数
   - {lean}`var n`，一个变量，编号为 {lean}`n`
   - {lean}`plus s t`，表示 {leanRef}`s` 和 {leanRef}`t` 的总和
   - {lean}`times s t`，表示 {leanRef}`s` 和 {leanRef}`t` 的乘积

--    Recursively define a function that evaluates any such term with respect to an assignment of values to the variables.

   递归地定义一个函数，根据变量的赋值来计算任何这样的项。

-- 4. Similarly, define the type of propositional formulas, as well as
--    functions on the type of such formulas: an evaluation function,
--    functions that measure the complexity of a formula, and a function
--    that substitutes another formula for a given variable.

4. 同样，定义命题公式的类型，以及关于这类公式类型的函数：求值函数、衡量公式复杂性的函数，以及用另一个公式替代给定变量的函数。
