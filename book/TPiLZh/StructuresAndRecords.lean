import VersoManual
import TPiLZh.Examples

open Verso.Genre Manual
open TPiLZh

set_option linter.typography.dashes false

#doc (Manual) "结构体和记录" =>
%%%
file := "StructuresAndRecords"
tag := "structures-and-records"
%%%
-- Structures and Records

-- We have seen that Lean's foundational system includes inductive
-- types. We have, moreover, noted that it is a remarkable fact that it
-- is possible to construct a substantial edifice of mathematics based on
-- nothing more than the type universes, dependent arrow types, and inductive types;
-- everything else follows from those. The Lean standard library contains
-- many instances of inductive types (e.g., {lean}`Nat`, {lean}`Prod`, {lean}`List`),
-- and even the logical connectives are defined using inductive types.

我们已经看到 Lean 的基本系统包括归纳类型。此外，显然仅基于类型宇宙、依赖箭头类型和归纳类型，
就有可能构建一个坚实的数学大厦；其他的一切都是由此而来。Lean 标准库包含许多归纳类型的实例
（例如，{lean}`Nat`，{lean}`Prod`，{lean}`List`），甚至逻辑连接词也是使用归纳类型定义的。

-- Recall that a non-recursive inductive type that contains only one
-- constructor is called a _structure_ or _record_. The product type is a
-- structure, as is the dependent product (Sigma) type.
-- In general, whenever we define a structure {lit}`S`, we usually
-- define _projection_ functions that allow us to “destruct” each
-- instance of {lit}`S` and retrieve the values that are stored in its
-- fields. The functions {lean}`Prod.fst` and {lean}`Prod.snd`, which return the
-- first and second elements of a pair, are examples of such projections.

回忆一下，只包含一个构造子的非递归归纳类型被称为 *结构体（structure）* 或 *记录（record）* 。
乘积类型是一种结构体，依值乘积（Sigma）类型也是如此。一般来说，每当我们定义一个结构体 {lit}`S` 时，
我们通常定义 *投影（projection）* 函数来“析构”（destruct）{lit}`S` 的每个实例并检索存储在其字段中的值。
{lean}`Prod.fst` 和 {lean}`Prod.snd`，分别返回乘积对中的第一个和第二个元素的函数，就是这种投影的例子。

-- When writing programs or formalizing mathematics, it is not uncommon
-- to define structures containing many fields. The {kw}`structure`
-- command, available in Lean, provides infrastructure to support this
-- process. When we define a structure using this command, Lean
-- automatically generates all the projection functions. The
-- {kw}`structure` command also allows us to define new structures based on
-- previously defined ones. Moreover, Lean provides convenient notation
-- for defining instances of a given structure.

在编写程序或形式化数学时，定义包含许多字段的结构体是很常见的。Lean 中可用 {kw}`structure` 命令实现此过程。
当我们使用这个命令定义一个结构体时，Lean 会自动生成所有的投影函数。{kw}`structure` 命令还允许我们根据以前定义的结构体定义新的结构体。
此外，Lean 为定义给定结构体的实例提供了方便的符号。

-- # Declaring Structures
# 声明结构体
%%%
tag := "declaring-structures"
%%%

-- The structure command is essentially a “front end” for defining
-- inductive data types. Every {kw}`structure` declaration introduces a
-- namespace with the same name. The general form is as follows:

结构体命令本质上是定义归纳数据类型的“前端”。每个 {kw}`structure` 声明都会引入一个同名的命名空间。一般形式如下：

-- ```
--     structure <name> <parameters> <parent-structures> where
--       <constructor> :: <fields>
-- ```

```
    structure <name> <parameters> <parent-structures> where
      <constructor> :: <fields>
```

-- Most parts are optional. Here is an example:

大多数部分不是必要的。例子：

:::setup
```lean
structure Point (α : Type u) where
  mk ::
  x : α
  y : α
  variable (p : Point α) (a b : α)
```
-- Values of type {leanRef}`Point` are created using {lean}`Point.mk a b`, and the
-- fields of a point {lean}`p` are accessed using {lean}`Point.x p` and
-- {lean}`Point.y p` (but {lean}`p.x` and {lean}`p.y` also work, see below).
-- The structure command also generates useful recursors and
-- theorems. Here are some of the constructions generated for the
-- declaration above.

类型 {leanRef}`Point` 的值是使用 {lean}`Point.mk a b` 创建的，并且点 {lean}`p` 的字段可以使用 {lean}`Point.x p` 和 {lean}`Point.y p`
（但 {lean}`p.x` 和 {lean}`p.y` 也可以，见下文）。结构体命令还生成有用的递归器和定理。下面是为上述声明生成的一些结构体方法。
:::

```lean
structure Point (α : Type u) where
  mk ::
  x : α
  y : α
------
-- a Type
-- 类型
#check Point

-- the eliminator
-- 消去器（eliminator）
#check @Point.rec

-- the constructor
-- 构造子
#check @Point.mk -- @Point.mk : {α : Type u_1} → α → α → Point α

-- a projection
-- 投影
#check @Point.x -- @Point.x : {α : Type u_1} → Point α → α

-- a projection
-- 投影
#check @Point.y -- @Point.y : {α : Type u_1} → Point α → α
```

-- If the constructor name is not provided, then a constructor is named
-- {lit}`mk` by default.

如果没有提供构造子名称，则默认的构造函数名为 {lit}`mk`。Point.mk : {α : Type u_1} → α → α → Point α

:::leanFirst
-- a projection
-- Here are some simple theorems and expressions that use the generated
-- constructions. As usual, you can avoid the prefix {leanRef}`Point` by using
-- the command {leanRef}`open Point`.

下面是一些使用生成的结构的简单定理和表达式。像往常一样，您可以通过使用命令 {leanRef}`open Point` 来避免前缀 {leanRef}`Point`。

```lean
structure Point (α : Type u) where
  x : α
  y : α
------
#eval Point.x (Point.mk 10 20) -- 10

#eval Point.y (Point.mk 10 20) -- 20

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl
```
:::


:::setup
```
structure Point (α : Type u) where
  x : α
  y : α
variable (p : Point Nat)
```


-- Given {lean}`p : Point Nat`, the dot notation {lean}`p.x` is shorthand for
-- {lean}`Point.x p`. This provides a convenient way of accessing the fields
-- of a structure.

给定 {lean}`p : Point Nat`，符号 {lean}`p.x` 是 {lean}`Point.x p` 的缩写。这提供了一种方便的方式来访问结构体的字段。
:::

```lean
structure Point (α : Type u) where
 x : α
 y : α
------
def p := Point.mk 10 20

#check p.x  -- p.x : Nat
#eval p.x   -- 10
#eval p.y   -- 20
```

Given {lean}`p : Point Nat`, the dot notation {lean}`p.x` is shorthand for
{lean}`Point.x p`. This provides a convenient way of accessing the fields
of a structure.

:::leanFirst
-- The dot notation is convenient not just for accessing the projections
-- of a record, but also for applying functions defined in a namespace
-- with the same name. Recall from the {ref "conjunction"}[Conjunction section] if {leanRef}`p`
-- has type {leanRef}`Point`, the expression {lit}`p.foo` is interpreted as
-- {lit}`Point.foo p`, assuming that the first non-implicit argument to
-- {lit}`foo` has type {leanRef}`Point`. The expression {leanRef}`p.add q` is therefore
-- shorthand for {lit}`Point.add p q` in the example below.

点记号不仅方便于访问记录的投影，而且也方便于应用同名命名空间中定义的函数。回想一下 {ref "conjunction"}[合取] 一节，如果 {leanRef}`p`
具有 {leanRef}`Point` 类型，那么表达式 {lit}`p.foo` 被解释为 {lit}`Point.foo p`，假设 {lit}`foo` 的第一个非隐式参数具有类型 {leanRef}`Point`。
因此下面的例子中，表达式 {leanRef}`p.add q` 是 {lit}`Point.add p q` 的缩写。

```lean
structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q  -- { x := 4, y := 6 }
```
:::

:::setup
```
structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

variable {α : Type u}
```

-- In the next chapter, you will learn how to define a function like
-- {leanRef}`add` so that it works generically for elements of {lean}`Point α`
-- rather than just {lean}`Point Nat`, assuming {lean}`α` has an associated
-- addition operation.

在下一章中，您将学习如何定义一个像 {leanRef}`add` 这样的函数，这样它就可以通用地为 {lean}`Point α` 的元素工作，
而不仅仅是 {lean}`Point Nat`，只要假设 {lean}`α` 有一个关联的加法操作。
:::

:::leanFirst
-- More generally, given an expression {lit}`p.foo x y z` where {lit}`p : Point`,
-- Lean will insert {lit}`p` at the first argument to {lit}`Point.foo` of type
-- {lit}`Point`. For example, with the definition of scalar multiplication
-- below, {leanRef}`p.smul 3` is interpreted as {leanRef}`Point.smul 3 p`.

更一般地，给定一个表达式 {lit}`p.foo x y z` 其中 {lit}`p : Point`，Lean 会把 {lit}`p` 以 {lit}`Point` 为类型插入到 {lit}`Point.foo` 的第一个参数。
例如，下面是标量乘法的定义，{leanRef}`p.smul 3` 被解释为 {leanRef}`Point.smul 3 p`。

```lean
structure Point (α : Type u) where
 x : α
 y : α
 deriving Repr
------
def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat := Point.mk 1 2

#eval p.smul 3  -- { x := 3, y := 6 }

example {p : Point Nat} : p.smul 3 = Point.smul 3 p := rfl
```
:::

-- It is common to use a similar trick with the {name}`List.map` function,
-- which takes a list as its second non-implicit argument:

对 {name}`List.map` 函数使用类似的技巧很常用。它接受一个列表作为它的第二个非隐式参数：

```lean
#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f  -- [1, 4, 9]

example {xs : List α} {f : α → β} :
    xs.map f = List.map f xs :=
  rfl
```

-- Here {leanRef}`xs.map f` is interpreted as {leanRef}`List.map f xs`.

此处 {leanRef}`xs.map f` 被解释为 {leanRef}`List.map f xs`。

-- # Objects
# 对象
%%%
tag := "objects"
%%%

-- We have been using constructors to create elements of a structure
-- type. For structures containing many fields, this is often
-- inconvenient, because we have to remember the order in which the
-- fields were defined. Lean therefore provides the following alternative
-- notations for defining elements of a structure type.

我们一直在使用构造子创建结构体类型的元素。对于包含许多字段的结构，这通常是不方便的，因为我们必须记住字段定义的顺序。
因此，Lean 为定义结构体类型的元素提供了以下替代符号。

-- ```
--     { (<field-name> := <expr>)* : structure-type }
--     or
--     { (<field-name> := <expr>)* }
-- ```

```
    { (<field-name> := <expr>)* : structure-type }
    or
    { (<field-name> := <expr>)* }
```

-- The suffix {lit}`: structure-type` can be omitted whenever the name of
-- the structure can be inferred from the expected type. For example, we
-- use this notation to define “points.” The order that the fields are
-- specified does not matter, so all the expressions below define the
-- same point.

只要可以从期望的类型推断出结构体的名称，后缀 {lit}`: structure-type` 就可以省略。例如，我们使用这种表示法来定义“Point”。
字段的指定顺序无关紧要，因此下面的所有表达式定义相同的 Point。

```lean
structure Point (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }  -- { x := 10, y := 20 } : Point Nat

#check { y := 20, x := 10 : Point _ } -- { x := 10, y := 20 } : Point Nat

#check ({ x := 10, y := 20 } : Point Nat) -- { x := 10, y := 20 } : Point Nat

example : Point Nat :=
  { y := 20, x := 10 }
```

-- Fields can be marked as implicit using curly braces.
-- Implicit fields become implicit parameters to the constructor.

可以使用花括号将字段标记为隐式。隐式字段将成为构造子的隐式参数。

-- If the value of a field is not specified, Lean tries to infer it. If
-- the unspecified fields cannot be inferred, Lean flags an error
-- indicating the corresponding placeholder could not be synthesized.

如果一个字段的值没有指定，Lean 会尝试推断它。如果不能推断出未指定的字段，Lean 会标记一个错误，表明相应的占位符无法合成。

```lean
structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

#check { a := 10, b := true : MyStruct }
```

-- _Record update_ is another common operation which amounts to creating
-- a new record object by modifying the value of one or more fields in an
-- old one. Lean allows you to specify that unassigned fields in the
-- specification of a record should be taken from a previously defined
-- structure object {lit}`s` by adding the annotation {lit}`s `{kw}`with` before the field
-- assignments. If more than one record object is provided, then they are
-- visited in order until Lean finds one that contains the unspecified
-- field. Lean raises an error if any of the field names remain
-- unspecified after all the objects are visited.

*记录更新（Record update）* 是另一个常见的操作，相当于通过修改旧记录中的一个或多个字段的值来创建一个新的记录对象。
通过在字段赋值之前添加注释 {lit}`s `{kw}`with`，Lean 允许您指定记录规范中未赋值的字段，该字段应从之前定义的结构对象 {lit}`s` 中获取。
如果提供了多个记录对象，那么将按顺序访问它们，直到 Lean 找到一个包含未指定字段的记录对象。
如果在访问了所有对象之后仍未指定任何字段名，Lean 将引发错误。

```lean
structure Point (α : Type u) where
  x : α
  y : α
deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }

#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl
```

-- # Inheritance
# 继承
%%%
tag := "inheritance"
%%%

-- We can _extend_ existing structures by adding new fields. This feature
-- allows us to simulate a form of _inheritance_.

我们可以通过添加新的字段来 *扩展* 现有的结构体。这个特性允许我们模拟一种形式的 *继承* 。

```lean
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color
```

-- In the next example, we define a structure using multiple inheritance,
-- and then define an object using objects of the parent structures.

在下一个例子中，我们使用多重继承定义一个结构体，然后使用父结构的对象定义一个对象。

```lean
structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
```
