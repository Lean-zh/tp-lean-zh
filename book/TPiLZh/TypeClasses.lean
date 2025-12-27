import VersoManual
import TPiLZh.Examples

open Verso.Genre
open Verso.Genre.Manual hiding tactic
open TPiLZh

set_option linter.typography.dashes false

#doc (Manual) "类型类" =>
%%%
tag := "type-classes"
file := "TypeClasses"
%%%
-- Type Classes

-- Type classes were introduced as a principled way of enabling
-- ad-hoc polymorphism in functional programming languages. We first observe that it
-- would be easy to implement an ad-hoc polymorphic function (such as addition) if the
-- function simply took the type-specific implementation of addition as an argument
-- and then called that implementation on the remaining arguments. For example,
-- suppose we declare a structure in Lean to hold implementations of addition.
类型类（Type Class）作为一种原则性方法引入，是为了在函数式编程语言中支持特设多态（Ad-hoc Polymorphism）。
我们首先观察到，如果函数简单地接受特定类型的实现作为参数，然后在其余参数上调用该实现，
则很容易实现特设多态函数（如加法）。例如，假设我们在 Lean 中声明一个结构体来保存加法的实现：

```lean
namespace Ex
------
structure Add (α : Type) where
  add : α → α → α

#check @Add.add -- @Add.add : {α : Type} → Add α → α → α → α
------
end Ex
```


::::setup
```
namespace Ex
structure Add (α : Type) where
  add : α → α → α
def double (s : Add α) (x : α) : α :=
  s.add x x
variable {n : Nat}
```
:::leanFirst
-- In the above Lean code, the field {leanRef}`add` has type
-- {lean}`Add.add : {α : Type} → Add α → α → α → α`
-- where the curly braces around the type {leanRef}`α` mean that it is an implicit argument.
-- We could implement {leanRef}`double` by:
在上面的 Lean 代码中，字段 {leanRef}`add` 的类型为
{lean}`Add.add : {α : Type} → Add α → α → α → α`
其中类型 {leanRef}`α` 周围的大括号表示它是一个隐式参数。我们可以通过以下方式实现 {leanRef}`double`：


```lean
namespace Ex
structure Add (α : Type) where
  add : α → α → α
------
def double (s : Add α) (x : α) : α :=
  s.add x x

#eval double { add := Nat.add } 10 -- 20

#eval double { add := Nat.mul } 10 -- 100

#eval double { add := Int.add } 10 -- 20
------
end Ex
```

:::

-- Note that you can double a natural number {lean}`n` by {lean}`double { add := Nat.add } n`.
-- Of course, it would be highly cumbersome for users to manually pass the
-- implementations around in this way.
-- Indeed, it would defeat most of the potential benefits of ad-hoc
-- polymorphism.
注意，你可以用 {lean}`double { add := Nat.add } n` 使一个自然数 {lean}`n` 翻倍。
当然，以这种方式让用户手动四处传递实现会非常繁琐。
实际上，这会消除掉特设多态的大部分潜在好处。
::::

:::leanFirst
-- The main idea behind type classes is to make arguments such as {leanRef}`Add α` implicit,
-- and to use a database of user-defined instances to synthesize the desired instances
-- automatically through a process known as typeclass resolution. In Lean, by changing
-- {kw}`structure` to {kw}`class` in the example above, the type of {leanRef}`Add.add` becomes:
类型类的主要思想是使诸如 {leanRef}`Add α` 之类的参数变为隐含的，
并使用用户定义实例的数据库通过称为类型类解析的过程自动合成所需的实例。
在 Lean 中，通过在以上示例中将 {kw}`structure` 更改为 {kw}`class`，{leanRef}`Add.add` 的类型会变为：

```lean
namespace Ex
------
class Add (α : Type) where
  add : α → α → α

#check @Add.add -- @Add.add : {α : Type} → [self : Add α] → α → α → α
------
end Ex
```
:::

-- where the square brackets indicate that the argument of type {leanRef}`Add α` is _instance implicit_,
-- i.e. that it should be synthesized using typeclass resolution. This version of
-- {leanRef}`add` is the Lean analogue of the Haskell term {lit}`add :: Add a => a -> a -> a`.
-- Similarly, we can register instances by:
其中方括号表示类型为 {leanRef}`Add α` 的参数是 _实例隐式的_ ，
即，它应该使用类型类解析合成。这个版本的 {leanRef}`add` 是 Haskell 项 {lit}`add :: Add a => a -> a -> a` 的 Lean 类比。
同样，我们可以通过以下方式注册实例：

```lean
namespace Ex
class Add (α : Type) where
  add : α → α → α
------
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add
------
end Ex
```

::::leanFirst
:::setup
```
namespace Ex
class Add (α : Type) where
  add : α → α → α
------
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add

variable (n m : Nat)
```
-- Then for {lean}`n : Nat` and {lean}`m : Nat`, the term {lean}`Add.add n m` triggers typeclass resolution with
-- the goal of {lean}`Add Nat`, and typeclass resolution will synthesize the instance for {lean}`Nat` above.
-- We can now reimplement {leanRef}`double` using an instance implicit by:
接着对于 {lean}`n : Nat` 和 {lean}`m : Nat`，项 {lean}`Add.add n m` 触发了类型类解析，
目标为 {lean}`Add Nat`，且类型类解析将综合上面 {lean}`Nat` 的实例。
现在，我们可以通过隐式的实例重新实现 {leanRef}`double` 了：
:::

```lean
namespace Ex
class Add (α : Type) where
  add : α → α → α
instance : Add Nat where
 add := Nat.add
instance : Add Int where
 add := Int.add
instance : Add Float where
 add := Float.add
------
def double [Add α] (x : α) : α :=
  Add.add x x

#check @double -- @double : {α : Type} → [Add α] → α → α

#eval double 10 -- 20

#eval double (10 : Int) -- 20

#eval double (7 : Float) -- 14.000000

#eval double (239.0 + 2) -- 482.000000

------
end Ex
```
::::

:::leanFirst
-- In general, instances may depend on other instances in complicated ways. For example,
-- you can declare an instance stating that if {leanRef}`α` has addition, then {leanRef}`Array α`
-- has addition:
一般情况下，实例可能以复杂的方式依赖于其他实例。例如，你可以声明一个实例，
说明如果 {leanRef}`α` 存在加法，那么 {leanRef}`Array α` 也存在加法：

```lean
instance [Add α] : Add (Array α) where
  add x y := Array.zipWith (· + ·) x y

#eval Add.add #[1, 2] #[3, 4] -- #[4, 6]

#eval #[1, 2] + #[3, 4] -- #[4, 6]
```
:::

-- Note that {leanRef}`(· + ·)` is notation for {lean}`fun x y => x + y` in Lean.
请注意，{leanRef}`(· + ·)` 是 Lean 中 {lean}`fun x y => x + y` 的记法。


:::setup
```
def head [Inhabited α] (xs : List α) : α := default
variable {α : Type u} {x : α} {xs : List α} [Inhabited α]
```

-- The example above demonstrates how type classes are used to overload notation.
-- Now, we explore another application. We often need an arbitrary element of a given type.
-- Recall that types may not have any elements in Lean.
-- It often happens that we would like a definition to return an arbitrary element in a “corner case.”
-- For example, we may like the expression {lean}`head xs` to be of type {lean}`α` when {lean}`xs` is of type {lean}`List α`.
-- Similarly, many theorems hold under the additional assumption that a type is not empty.
-- For example, if {lean}`α` is a type, {lean}`∃ x : α, x = x` is true only if {lean}`α` is not empty.
-- The standard library defines a type class {lean}`Inhabited` to enable type class inference to infer a
-- “default” element of an inhabited type.
-- Let us start with the first step of the program above, declaring an appropriate class:
上述示例演示了类型类如何用于重载符号。现在，我们探索另一个应用程序。
我们经常需要给定类型的任意元素。回想一下类型在 Lean 中可能没有任何元素。
我们经常希望在一个“边界情况”下定义返回一个任意元素。
例如，我们可能希望当 {lean}`xs` 为 {lean}`List α` 类型时 {lean}`head xs` 表达式的类型为 {lean}`α`。
类似地，许多定理在类型不为空的附加假设下成立。例如，如果 {lean}`α` 是一个类型，
则 {lean}`∃ x : α, x = x` 仅在 {lean}`α` 不为空时为真。标准库定义了一个类型类
{lean}`Inhabited`，它能够让类型类推理来推断 _可居（Inhabited）_ 类型类的“默认”元素。
让我们从上述程序的第一步开始，声明一个适当的类：



```lean
namespace Ex
------
class Inhabited (α : Type u) where
  default : α

#check @Inhabited.default -- @Inhabited.default : {α : Type u_1} → [self : Inhabited α] → α
------
end Ex
```

-- Note {leanRef}`Inhabited.default` doesn't have any explicit arguments.
注意 {leanRef}`Inhabited.default` 没有任何显式参数。

-- An element of the class {lean}`Inhabited α` is simply an expression of the form {lean}`Inhabited.mk x`, for some element {lean}`x : α`.
-- The projection {lean}`Inhabited.default` will allow us to “extract” such an element of {lean}`α` from an element of {lean}`Inhabited α`.
-- Now we populate the class with some instances:
类 {lean}`Inhabited α` 的某个元素只是形式为 {lean}`Inhabited.mk x` 的表达式，
其中 {lean}`x : α` 为某个元素。投影 {lean}`Inhabited.default` 可让我们从 {lean}`Inhabited α`
的某个元素中“提取”出 {lean}`α` 的某个元素。现在我们用一些实例填充该类：
:::

```lean
namespace Ex
class Inhabited (a : Type _) where
 default : a
------
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat) -- 0

#eval (Inhabited.default : Bool) -- true
--------
end Ex
```

-- You can use the command {kw}`export` to create the alias {lean}`default` for {lean}`Inhabited.default`.
你可以用 {kw}`export` 命令来为 {lean}`Inhabited.default` 创建别名 {lean}`default`。

```lean
namespace Ex
class Inhabited (a : Type _) where
 default : a
instance : Inhabited Bool where
 default := true
instance : Inhabited Nat where
 default := 0
instance : Inhabited Unit where
 default := ()
instance : Inhabited Prop where
 default := True
------
export Inhabited (default)

#eval (default : Nat) -- 0

#eval (default : Bool) -- true
------
end Ex
```

-- # Chaining Instances
# 链接实例
%%%
tag := "chaining-instances"
%%%

-- If that were the extent of type class inference, it would not be all that impressive;
-- it would be simply a mechanism of storing a list of instances for the elaborator to find in a lookup table.
-- What makes type class inference powerful is that one can _chain_ instances. That is,
-- an instance declaration can in turn depend on an implicit instance of a type class.
-- This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.
以类型类推断的层面来看，它并不那么令人印象深刻；
它不过是一种为精细器存储实例列表的机制，用于在查询表中查找。
类型类推断变得强大的原因在于，它能够“链接（Chain）”实例。也就是说，
实例声明本身可以依赖类型类的隐式实例。
这导致类推断递归地通过实例进行链接，并在必要时回溯，就像 Prolog 中的搜索一样。

:::leanFirst
-- For example, the following definition shows that if two types {leanRef}`α` and {leanRef}`β` are inhabited, then so is their product:
例如，以下定义展示了若两个类型 {leanRef}`α` 和 {leanRef}`β` 包含元素，则二者的积也包含元素：

```lean
instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)
```
:::

-- With this added to the earlier instance declarations, type class instance can infer, for example, a default element of {lean}`Nat × Bool`:
将它添加到先前的实例声明后，类型类实例就能推导了，例如 {lean}`Nat × Bool` 的默认元素为：

```lean
namespace Ex
class Inhabited (α : Type u) where
 default : α
instance : Inhabited Bool where
 default := true
instance : Inhabited Nat where
 default := 0
opaque default [Inhabited α] : α :=
 Inhabited.default
------
instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (default, default)

#eval (default : Nat × Bool) -- (0, true)
------
end Ex
```

-- Similarly, we can inhabit type function with suitable constant functions:
与此类似，我们可以使用合适的常量函数使其居留到类型函数中：

```lean
instance [Inhabited β] : Inhabited (α → β) where
  default := fun _ => default
```

-- As an exercise, try defining default instances for other types, such as {lean}`List` and {lean}`Sum` types.
作为练习，请尝试为其他类型定义默认实例，例如 {lean}`List` 和 {lean}`Sum` 类型。

:::setup
```
universe u
set_option checkBinderAnnotations false
```
-- The Lean standard library contains the definition {name}`inferInstance`. It has type {lean}`{α : Sort u} → [i : α] → α`,
-- and is useful for triggering the type class resolution procedure when the expected type is an instance.
Lean 标准库包含了定义 {name}`inferInstance`，它的类型为 {lean}`{α : Sort u} → [i : α] → α`，
它在期望的类型是一个实例时触发类型类解析过程十分有用。
:::

```lean
#check (inferInstance : Inhabited Nat) -- inferInstance : Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) :=
  rfl
```

:::leanFirst
-- You can use the command {leanRef}`#print` to inspect how simple {leanRef}`inferInstance` is.
你可以使用命令 {leanRef}`#print` 来检查 {leanRef}`inferInstance` 有多简单。

```lean
#print inferInstance
```
:::

-- # ToString
# ToString 方法
%%%
tag := "ToString"
%%%
```setup
universe u
```

:::leanFirst
-- The polymorphic method {leanRef}`toString` has type {lean}`{α : Type u} → [ToString α] → α → String`. You implement the instance
-- for your own types and use chaining to convert complex values into strings. Lean comes with {lean}`ToString` instances
-- for most builtin types.
多态方法 {leanRef}`toString` 类型为 {lean}`{α : Type u} → [ToString α] → α → String`。
你可以为自己的类型实现实例并使用链接将复杂的值转换为字符串。
Lean 为大多数内置类型都提供了 {lean}`ToString` 实例。

```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person } -- "Leo@542"

#eval toString ({ name := "Daniel", age := 18 : Person }, "hello") -- "(Daniel@18, hello)"
```
:::

-- # Numerals
# 数值
%%%
tag := "numerals"
%%%

-- Numerals are polymorphic in Lean. You can use a numeral (e.g., {lit}`2`) to denote an element of any type that implements
-- the type class {name}`OfNat`.
数值在 Lean 中是多态的。你可以用一个数值（例如 {lit}`2`）来表示任何实现了类型类
{name}`OfNat` 的类型中的一个元素。

```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check (2 : Rational) -- 2 : Rational

#check (2 : Nat)      -- 2 : Nat
```

:::setup
```
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"
```
-- Lean elaborates the terms {lean}`(2 : Nat)` and {lean}`(2 : Rational)` as
-- {lean (type := "Nat")}`@OfNat.ofNat Nat 2 (@instOfNatNat 2)` and
-- {lean}`@OfNat.ofNat Rational 2 (@instOfNatRational 2)` respectively.
-- We say the numerals {lit}`2` occurring in the elaborated terms are _raw_ natural numbers.
-- You can input the raw natural number {lit}`2` using the macro {lean}`nat_lit 2`.
Lean 会将项 {lean}`(2 : Nat)` 和 {lean}`(2 : Rational)` 分别繁饰（Elaborate）为：
{lean (type := "Nat")}`@OfNat.ofNat Nat 2 (@instOfNatNat 2)` 和
{lean}`@OfNat.ofNat Rational 2 (@instOfNatRational 2)`。
我们将繁饰的项中出现的数字 {lit}`2` 称为 _原始_ 自然数。
你可以使用宏 {lean}`nat_lit 2` 来输入原始自然数 {lit}`2`。
:::

```lean
#check nat_lit 2  -- 2 : Nat
```

-- Raw natural numbers are _not_ polymorphic.
原始自然数 _不是_ 多态的。

-- The {lean}`OfNat` instance is parametric on the numeral. So, you can define instances for particular numerals.
-- The second argument is often a variable as in the example above, or a _raw_ natural number.
{lean}`OfNat` 实例对数值进行了参数化，因此你可以定义特定数字的实例。
第二个参数通常是变量，如上例所示，或者是一个 _原始_ 自然数。

```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

-- # Output Parameters
# 输出参数
%%%
tag := "output-parameters"
%%%

:::setup
```
universe u
variable (T : Type u)
```

-- By default, Lean only tries to synthesize an instance {lean}`Inhabited T` when the term {lean}`T` is known and does not
-- contain missing parts. The following command produces the error
-- {lit}`typeclass instance problem is stuck, it is often due to metavariables` because the type has a missing part (i.e., the {lit}`_`).
默认情况下，Lean 仅当项 {lean}`T` 已知时且不包含缺失部分时，会尝试合成实例 {lean}`Inhabited T`。
以下命令会产生错误“{lit}`typeclass instance problem is stuck, it is often due to metavariables`
（类型类实例问题卡住了，通常是由于元变量引起的）”，因为该类型有缺失的部分（即 {lit}`_`）。
:::

```lean
/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Inhabited (Nat × ?m.2)
-/
#guard_msgs (error) in
#eval (inferInstance : Inhabited (Nat × _))
```

-- You can view the parameter of the type class {lean}`Inhabited` as an _input_ value for the type class synthesizer.
-- When a type class has multiple parameters, you can mark some of them as {deftech}_output parameters_.
-- Lean will start type class synthesizer even when these parameters have missing parts.
-- In the following example, we use output parameters to define a _heterogeneous_ polymorphic
-- multiplication.
你可以将类型类 {lean}`Inhabited` 的参数视为类型类合成器的 _输入_ 值。
当类型类有多个参数时，可以将其中一些标记为 {deftech}_输出参数_ （Output Parameter）。
即使这些参数有缺失部分，Lean 也会开始类型类合成。
在下面的示例中，我们使用输出参数定义一个 _异质（Heterogeneous）_ 的多态乘法。

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12

#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
------
end Ex
```

-- The parameters {leanRef}`α` and {leanRef}`β` are considered input parameters and {leanRef}`γ` an output one.
-- Given an application {leanRef}`hMul a b`, after the types of {leanRef}`a` and {leanRef}`b` are known, the type class
-- synthesizer is invoked, and the resulting type is obtained from the output parameter {leanRef}`γ`.
-- In the example above, we defined two instances. The first one is the homogeneous
-- multiplication for natural numbers. The second is the scalar multiplication for arrays.
-- Note that you chain instances and generalize the second instance.
参数 {leanRef}`α` 和 {leanRef}`β` 会被视为输入参数，{leanRef}`γ` 被视为输出参数。
如果给定一个应用 {leanRef}`hMul a b`，那么在知道 {leanRef}`a` 和 {leanRef}`b` 的类型后，
将调用类型类合成器，并且可以从输出参数 {leanRef}`γ` 中获得最终的类型。
在上文中的示例中，我们定义了两个实例。第一个实例是针对自然数的同质乘法。
第二个实例是针对数组的标量乘法。请注意，你可以链接实例，并推广第二个实例。

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12

#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]

#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]

#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]
------
end Ex
```

-- You can use our new scalar array multiplication instance on arrays of type {leanRef}`Array β`
-- with a scalar of type {leanRef}`α` whenever you have an instance {leanRef}`HMul α β γ`.
-- In the last {kw}`#eval`, note that the instance was used twice on an array of arrays.
当你拥有 {leanRef}`HMul α β γ` 的实例时，可以在类型为 {leanRef}`Array β` 的数组上将其使用标量类型
{leanRef}`α` 的新标量数组乘法实例。在最后的 {kw}`#eval` 中，请注意该实例曾在数组数组中使用了两次。

-- Output parameters are ignored during instance synthesis. Even when instance synthesis occurs in a
-- context in which the values of output parameters are already determined, their values are ignored.
-- Once an instance is found using its input parameters, Lean ensures that the already-known values of
-- the output parameters match those which were found.
输出参数在实例合成期间被忽略。即使实例合成发生在输出参数的值已经确定的上下文中，它们的值也会被忽略。
一旦使用其输入参数找到实例，Lean 就会确保输出参数的已知值与找到的值匹配。

-- Lean also features {deftech}_semi-output parameters_, which have some features of input parameters
-- and some features of output parameters. Like input parameters, semi-output parameters are considered
-- when selecting instances. Like output parameters, they can be used to instantiate unknown values.
-- However, they do not do so uniquely. Instance synthesis with semi-output parameters can be more difficult
-- to predict, because the order in which instances are considered can determine which is selected, but it is
-- also more flexible.
Lean 还具有 {deftech}_半输出参数_ （Semi-output Parameter），它具有输入参数的一些特征和输出参数的一些特征。
与输入参数一样，在选择实例时会考虑半输出参数。与输出参数一样，它们可以用于实例化未知值。
然而，它们并不唯一地这样做。使用半输出参数进行实例合成可能更难以预测，
因为考虑实例的顺序可以决定选择哪一个，但它也更灵活。

-- # Default Instances
# 默认实例
%%%
tag := "default-instances"
%%%

-- In the class {leanRef}`HMul`, the parameters {leanRef}`α` and {leanRef}`β` are treated as input values.
-- Thus, type class synthesis only starts after these two types are known. This may often
-- be too restrictive.
在类 {leanRef}`HMul` 中，参数 {leanRef}`α` 和 {leanRef}`β` 被当做输入值。
因此，类型类合成仅在已知这两种类型时才开始。这通常可能过于严格。

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

/--
error: typeclass instance problem is stuck
  HMul Int ?m.2 (?m.11 y)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `HMul` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs (error) in
#eval fun y => xs.map (fun x => hMul x y)
------
end Ex
```

-- The instance {leanRef}`HMul` is not synthesized by Lean because the type of {leanRef}`y` has not been provided.
-- However, it is natural to assume that the type of {leanRef}`y` and {leanRef}`x` should be the same in
-- this kind of situation. We can achieve exactly that using _default instances_.
实例 {leanRef}`HMul` 没有被 Lean 合成，因为没有提供 {leanRef}`y` 的类型。
然而，在这种情况下，自然应该认为 {leanRef}`y` 和 {leanRef}`x` 的类型应该相同。
我们可以使用 _默认实例_ 来实现这一点。

```lean
namespace Ex
------
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)  -- fun y => List.map (fun x => hMul x y) xs : Int → List Int
------
end Ex
```

:::setup
```
variable {α : Type u} {β : Type v} {γ : Type w} {a : α} {b : β} {n : Nat}
variable [HAdd α β γ] [HSub α β γ] [HMul α β γ] [HDiv α β γ] [HMod α β γ]
```
-- By tagging the instance above with the attribute {attr}`[default_instance]`, we are instructing Lean
-- to use this instance on pending type class synthesis problems.
-- The actual Lean implementation defines homogeneous and heterogeneous classes for arithmetical operators.
-- Moreover, {lean}`a + b`, {lean}`a * b`, {lean}`a - b`, {lean}`a / b`, and {lean}`a % b` are notations for the heterogeneous versions.
-- The instance {lean}`OfNat Nat n` is the default instance (with priority 100) for the {lean}`OfNat` class. This is why the numeral
-- {lean}`2` has type {lean}`Nat` when the expected type is not known. You can define default instances with higher
-- priority to override the builtin ones.
通过给上述实例添加 {attr}`[default_instance]` 属性，我们指示 Lean 在挂起的类型类合成问题中使用此实例。
实际的 Lean 实现为算术运算符定义了同质和异质类。此外，{lean}`a + b`、{lean}`a * b`、{lean}`a - b`、{lean}`a / b` 和 {lean}`a % b`
是异质版本的记法。实例 {lean}`OfNat Nat n` 是 {lean}`OfNat` 类的默认实例（优先级 100）。
这就是当预期类型未知时，数字 {lean}`2` 具有类型 {lean}`Nat` 的原因。
你可以定义具有更高优先级的默认实例来覆盖内置实例。
:::
```lean
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[default_instance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- 2 : Rational
```

:::setup
```
variable {α : Type u} {xs : List α} [Mul α] [OfNat α 2]
```

-- Priorities are also useful to control the interaction between different default instances.
-- For example, suppose {lean}`xs` has type {lean}`List α`. When elaborating {lean}`xs.map (fun x => 2 * x)`, we want the homogeneous instance for multiplication
-- to have higher priority than the default instance for {lean}`OfNat α 2`. This is particularly important when we have implemented only the instance
-- {lean}`HMul α α α`, and did not implement {lean}`HMul Nat α α`.
-- Now, we reveal how the notation {lit}`a * b` is defined in Lean.
优先级也适用于控制不同默认实例之间的交互。例如，假设 {lean}`xs` 有类型 {lean}`List α`。
在繁饰 {lean}`xs.map (fun x => 2 * x)` 时，我们希望乘法的同质实例比 {lean}`OfNat α 2`
的默认实例具有更高的优先级。当我们仅实现了实例 {lean}`HMul α α α`，而未实现 {lean}`HMul Nat α α` 时，
这一点尤为重要。现在，我们展示了 {lit}`a * b` 记法在 Lean 中是如何定义的。
:::
```lean
namespace Ex
------
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * " => HMul.hMul
------
end Ex
```

-- The {leanRef}`Mul` class is convenient for types that only implement the homogeneous multiplication.
{leanRef}`Mul` 类是仅实现了同质乘法的类型的简便记法。

-- # Local Instances
# 局部实例
%%%
tag := "local-instances"
%%%

-- Type classes are implemented using attributes in Lean. Thus, you can
-- use the {kw}`local` modifier to indicate that they only have effect until
-- the current {kw}`section` or {kw}`namespace` is closed, or until the end
-- of the current file.
类型类是使用 Lean 中的属性（Attribute）来实现的。因此，你可以使用 {kw}`local`
修饰符表明它们只对当前 {kw}`section` 或 {kw}`namespace` 关闭之前或当前文件结束之前有效。

```lean
structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end -- instance `Add Point` is not active anymore

/--
error: failed to synthesize
  HAdd Point Point ?m.5

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command.
-/
#guard_msgs in
def triple (p : Point) :=
  p + p + p
```

-- You can also temporarily disable an instance using the {kw}`attribute` command
-- until the current {kw}`section` or {kw}`namespace` is closed, or until the end
-- of the current file.
你也可使用 {kw}`attribute` 命令暂时禁用一个实例，直至当前的 {kw}`section` 或
{kw}`namespace` 关闭，或直到当前文件的结尾。

```lean
structure Point where
  x : Nat
  y : Nat

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

attribute [-instance] addPoint

/--
error: failed to synthesize
  HAdd Point Point ?m.5

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command.
-/
#guard_msgs in
def triple (p : Point) :=
  p + p + p  -- Error: failed to synthesize instance
```

-- We recommend you only use this command to diagnose problems.
我们建议你只使用此命令来诊断问题。

-- # Scoped Instances
# 作用域实例
%%%
tag := "scoped-instances"
%%%

-- You can also declare scoped instances in namespaces. This kind of instance is
-- only active when you are inside of the namespace or open the namespace.
你可以在命名空间中声明作用域实例。这种类型的实例只在你进入命名空间或打开命名空间时激活。

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point
-- instance `Add Point` is not active anymore

/--
error: failed to synthesize
  HAdd Point Point ?m.3

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command.
-/
#guard_msgs (error) in
#check fun (p : Point) => p + p + p

namespace Point
-- instance `Add Point` is active again
#check fun (p : Point) => p + p + p

end Point

open Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p
```

-- You can use the command {kw}`open scoped`{lit}` <namespace>` to activate scoped attributes but will
-- not “open” the names from the namespace.
你可以使用 {kw}`open scoped`{lit}` <namespace>` 命令来激活作用域内的属性，但不会“打开”命名空间中的名称。

```lean
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point

open scoped Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p

/--
error: Unknown identifier `double`
-/
#guard_msgs (error) in
#check fun (p : Point) => double p
```

-- # Decidable Propositions
# 可判定的命题
%%%
tag := "decidable-propositions"
%%%

-- Let us consider another example of a type class defined in the
-- standard library, namely the type class of {lean}`Decidable`
-- propositions. Roughly speaking, an element of {lean}`Prop` is said to be
-- decidable if we can decide whether it is true or false. The
-- distinction is only useful in constructive mathematics; classically,
-- every proposition is decidable. But if we use the classical principle,
-- say, to define a function by cases, that function will not be
-- computable. Algorithmically speaking, the {lean}`Decidable` type class can
-- be used to infer a procedure that effectively determines whether or
-- not the proposition is true. As a result, the type class supports such
-- computational definitions when they are possible while at the same
-- time allowing a smooth transition to the use of classical definitions
-- and classical reasoning.
让我们考虑标准库中定义的另一个类型类，名为 {lean}`Decidable` 类型类。
粗略地讲，对于 {lean}`Prop` 的一个元素，如果我们可以判定它是真或假，它就被称为可判定的。
这种区别只有在构造性数学中才有用；在经典数学中，每个命题都是可判定的。
但如果我们使用经典原则，比如通过情况来定义一个函数，那么这个函数将不可计算。
从算法上来讲，{lean}`Decidable` 类型类可以用来推导出一个过程，它能有效判定命题是否为真。
因此，该类型类支持这样的计算性定义（如果它们是可能的），
同时还允许平滑地过渡到经典定义和经典推理的使用。

-- In the standard library, {lean}`Decidable` is defined formally as follows:
在标准库中，{lean}`Decidable` 的形式化定义如下：

```lean
namespace Hidden
------
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
------
end Hidden
```

:::setup
```
variable {p : Prop} (t : Decidable p) (t' : p ∨ ¬p) (a b : α)
```

-- Logically speaking, having an element {lean}`t : Decidable p` is stronger
-- than having an element {lean}`t' : p ∨ ¬p`; it enables us to define values
-- of an arbitrary type depending on the truth value of {lean}`p`. For
-- example, for the expression {lean}`if p then a else b` to make sense, we
-- need to know that {lean}`p` is decidable. That expression is syntactic
-- sugar for {lean}`ite p a b`, where {lean}`ite` is defined as follows:
从逻辑上讲，拥有一个元素 {lean}`t : Decidable p` 比拥有一个元素 {lean}`t' : p ∨ ¬p` 更强；
它允许我们定义一个任意类型的值，这些值取决于 {lean}`p` 的真值。
例如，为了使表达式 {lean}`if p then a else b` 有意义，我们需要知道 {lean}`p`
是可判定的。该表达式是 {lean}`ite p a b` 的语法糖，其中 {lean}`ite` 的定义如下：
:::
```lean
namespace Hidden
------
def ite {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t e : α) : α :=
  h.casesOn (motive := fun _ => α) (fun _ => e) (fun _ => t)
------
end Hidden
```

:::leanFirst
-- The standard library also contains a variant of {leanRef}`ite` called
-- {leanRef}`dite`, the dependent if-then-else expression. It is defined as
-- follows:
标准库中还包含 {leanRef}`ite` 的一种变体，称为 {leanRef}`dite`，
即依赖 if-then-else 表达式。它的定义如下：

```lean
namespace Hidden
------
def dite {α : Sort u}
    (c : Prop) [h : Decidable c]
    (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
------
end Hidden
```
:::

:::setup
```
variable {c : Prop} [Decidable c] (t : c → α) (e : ¬c → α) (hc : c) (hnc : ¬c)
```
```lean (show := false)
example [Decidable c] (t e : α) : α := if h : c then t else e
```

-- That is, in {lean}`dite c t e`, we can assume {lean}`hc : c` in the “then”
-- branch, and {lean}`hnc : ¬c` in the “else” branch. To make {lean}`dite` more
-- convenient to use, Lean allows us to write {leanRef}`if h : c then t else e`
-- instead of {lean}`dite c (fun h : c => t h) (fun h : ¬c => e h)`.
即在 {lean}`dite c t e` 表达式中，我们可以在 “then” 分支假定 {lean}`hc : c`，
在 “else” 分支假定 {lean}`hnc : ¬c`。为了方便 {lean}`dite` 的使用，
Lean 允许我们将 {leanRef}`if h : c then t else e` 写作 {lean}`dite c (fun h : c => t h) (fun h : ¬c => e h)`。
:::

-- Without classical logic, we cannot prove that every proposition is
-- decidable. But we can prove that _certain_ propositions are
-- decidable. For example, we can prove the decidability of basic
-- operations like equality and comparisons on the natural numbers and
-- the integers. Moreover, decidability is preserved under propositional
-- connectives:
如果没有经典逻辑，我们就不能证明每个命题都是可判定的。
但我们可以证明 _某些_ 命题是可判定的。
例如，我们可以证明基本运算（比如自然数和整数上的等式和比较）的可判定性。
此外，命题连词下的可判定性被保留了下来：

```lean
#check @instDecidableAnd -- @instDecidableAnd : {p q : Prop} → [dp : Decidable p] → [dq : Decidable q] → Decidable (p ∧ q)

#check @instDecidableOr
#check @instDecidableNot
```

-- Thus we can carry out definitions by cases on decidable predicates on
-- the natural numbers:
因此，我们可以对自然数上的可判定谓词进行分情况定义：

```lean
def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step
```

-- Turning on implicit arguments shows that the elaborator has inferred
-- the decidability of the proposition {leanRef}`x < a ∨ x > b`, simply by
-- applying appropriate instances.
打开隐式参数显示，阐释器（Elaborator）已经通过应用适当的实例推导出了命题 {leanRef}`x < a ∨ x > b` 的可判定性。

-- With the classical axioms, we can prove that every proposition is
-- decidable. You can import the classical axioms and make the generic
-- instance of decidability available by opening the {lit}`Classical` namespace.
利用经典公理，我们可以证明每个命题都是可判定的。
你可以导入经典公理，并通过打开 {lit}`Classical` 命名空间来使通用的可判定性实例可用。

```lean
open Classical
```

:::setup
```
open Classical
variable {p : Prop}
```
-- Thereafter {lean}`Decidable p` has an instance for every {leanRef}`p`.
-- Thus all theorems in the library
-- that rely on decidability assumptions are freely available when you
-- want to reason classically. In {ref "axioms-and-computation"}[Axioms and Computation],
-- we will see that using the law of the
-- excluded middle to define functions can prevent them from being used
-- computationally. Thus, the standard library assigns a low priority to
-- the {lean}`propDecidable` instance.
此后，对于每个 {leanRef}`p`，{lean}`Decidable p` 都有一个实例。
因此，当你想要进行经典推理时，库中所有依赖于可判定性假设的定理都是可以自由使用的。
在 {ref "axioms-and-computation"}[公理与计算] 中，
我们将看到使用排中律来定义函数可能会阻止它们被用于计算。
因此，标准库为 {lean}`propDecidable` 实例分配了低优先级。
:::

```lean
namespace Hidden
------
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
------
end Hidden
```

-- This guarantees that Lean will favor other instances and fall back on
-- {leanRef}`propDecidable` only after other attempts to infer decidability have
-- failed.
这保证了 Lean 会优先选择其他实例，并且只有在其他推导可判定性的尝试失败后，
才会回退到 {leanRef}`propDecidable`。

-- The {lean}`Decidable` type class also provides a bit of small-scale
-- automation for proving theorems. The standard library introduces the
-- tactic {tactic}`decide` that uses the {lean}`Decidable` instance to solve simple goals,
-- as well as a function {name}`decide` that uses a {lean}`Decidable` instance to compute the
-- corresponding {lean}`Bool`.
{lean}`Decidable` 类型类还为证明定理提供了一些小规模的自动化。
标准库引入了 {tactic}`decide` 策略，它使用 {lean}`Decidable` 实例来解决简单的目标，
以及一个 {name}`decide` 函数，它使用 {lean}`Decidable` 实例来计算相应的 {lean}`Bool`。

```lean
example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬(True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1 + 1 := by
  decide

#print ex

#check @of_decide_eq_true -- @of_decide_eq_true : ∀ {p : Prop} [inst : Decidable p], decide p = true → p

#check @decide -- decide : (p : Prop) → [h : Decidable p] → Bool
```

:::setup
```
variable {p : Prop} [Decidable p]
```

-- They work as follows. The expression {lean}`decide p` tries to infer a
-- decision procedure for {leanRef}`p`, and, if it is successful, evaluates to
-- either {lean}`true` or {lean}`false`. In particular, if {leanRef}`p` is a true closed
-- expression, {leanRef}`decide p` will reduce definitionally to the Boolean {lean}`true`.
-- On the assumption that {lean}`decide p = true` holds, {lean}`of_decide_eq_true`
-- produces a proof of {lean}`p`. The tactic {tactic}`decide` puts it all together to
-- prove a target {lean}`p`. By the previous observations,
-- {tactic}`decide` will succeed any time the inferred decision procedure
--  for {lean}`p` has enough information to evaluate, definitionally, to the {lean}`isTrue` case.
它们的工作原理如下。表达式 {lean}`decide p` 尝试为 {leanRef}`p` 推导一个判定过程，
如果成功，则求值为 {lean}`true` 或 {lean}`false`。特别地，如果 {leanRef}`p` 是一个真的闭表达式，
{leanRef}`decide p` 将在定义上归约为布尔值 {lean}`true`。在 {lean}`decide p = true` 成立的假设下，
{lean}`of_decide_eq_true` 产生一个 {lean}`p` 的证明。{tactic}`decide` 策略将这一切结合起来证明目标 {lean}`p`。
根据之前的观察，只要为 {lean}`p` 推导出的判定过程有足够的信息在定义上求值为 {lean}`isTrue` 情况，
{tactic}`decide` 就会成功。
:::

-- # Managing Type Class Inference
# 管理类型类推导
%%%
tag := "managing-type-class-inference"
%%%

-- If you are ever in a situation where you need to supply an expression
-- that Lean can infer by type class inference, you can ask Lean to carry
-- out the inference using {name}`inferInstance`:
如果你遇到需要提供一个 Lean 可以通过类型类推导出的表达式的情况，
你可以要求 Lean 使用 {name}`inferInstance` 来执行推导：

```lean
def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance -- @inferInstance : {α : Sort u_1} → [i : α] → α
```

:::setup
```
variable (t : T)
```

-- In fact, you can use Lean's {lean}`(t : T)` notation to specify the class whose instance you are looking for,
-- in a concise manner:
事实上，你可以使用 Lean 的 {lean}`(t : T)` 符号来简洁地指定你正在寻找其实例的类：
:::

```lean
#check (inferInstance : Add Nat)
```

-- You can also use the auxiliary definition {lean}`inferInstanceAs`:
你也可以使用辅助定义 {lean}`inferInstanceAs`：

```lean
#check inferInstanceAs (Add Nat)

#check @inferInstanceAs -- inferInstanceAs : (α : Sort u_1) → [i : α] → α
```

:::leanFirst
-- Sometimes Lean can't find an instance because the class is buried
-- under a definition. For example, Lean cannot
-- find an instance of {leanRef}`Inhabited (Set α)`. We can declare one
-- explicitly:
有时 Lean 找不到实例，因为该类被埋在定义之下。例如，Lean 找不到 {leanRef}`Inhabited (Set α)` 的实例。
我们可以显式声明一个：

```lean
def Set (α : Type u) := α → Prop

/--
error: failed to synthesize
  Inhabited (Set α)

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command.
-/
#guard_msgs in
example : Inhabited (Set α) :=
  inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))
```
:::

-- At times, you may find that the type class inference fails to find an
-- expected instance, or, worse, falls into an infinite loop and times
-- out. To help debug in these situations, Lean enables you to request a
-- trace of the search:
有时，你可能会发现类型类推导无法找到预期的实例，或者更糟糕的是，陷入无限循环并超时。
为了在这些情况下帮助调试，Lean 允许你请求搜索的追踪：

```lean
set_option trace.Meta.synthInstance true
```

-- If you are using VS Code, you can read the results by hovering over
-- the relevant theorem or definition, or opening the messages window
-- with {kbd}[`Ctrl` `Shift` `Enter`].
如果你使用的是 VS Code，你可以通过将鼠标悬停在相关的定理或定义上，
或者使用 {kbd}[`Ctrl` `Shift` `Enter`] 打开消息窗口来读取结果。

-- You can also limit the search using the following options:
你还可以使用以下选项限制搜索：

```lean
set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
```

-- Option {option}`synthInstance.maxHeartbeats` specifies the maximum amount of
-- heartbeats per typeclass resolution problem. A heartbeat is the number of
-- (small) memory allocations (in thousands), 0 means there is no limit.
-- Option {option}`synthInstance.maxSize` is the maximum number of instances used
-- to construct a solution in the type class instance synthesis procedure.
选项 {option}`synthInstance.maxHeartbeats` 指定了每个类型类解析问题的最大心跳数。
心跳是（小的）内存分配次数（以千为单位），0 表示没有限制。
选项 {option}`synthInstance.maxSize` 是在类型类实例合成过程中用于构造解决方案的最大实例数。

-- Remember also that in both the VS Code and Emacs editor modes, tab
-- completion works in {kw}`set_option`, to help you find suitable options.
还要记住，在 VS Code 和 Emacs 编辑器模式下，Tab 补全在 {kw}`set_option` 中都有效，
可以帮助你找到合适的选项。

-- As noted above, the type class instances in a given context represent
-- a Prolog-like program, which gives rise to a backtracking search. Both
-- the efficiency of the program and the solutions that are found can
-- depend on the order in which the system tries the instance. Instances
-- which are declared last are tried first. Moreover, if instances are
-- declared in other modules, the order in which they are tried depends
-- on the order in which namespaces are opened. Instances declared in
-- namespaces which are opened later are tried earlier.
如上所述，给定上下文中的类型类实例代表一个类似于 Prolog 的程序，它会引起回溯搜索。
程序的效率和找到的解决方案都取决于系统尝试实例的顺序。最后声明的实例最先被尝试。
此外，如果实例是在其他模块中声明的，则尝试它们的顺序取决于打开命名空间的顺序。
在较晚打开的命名空间中声明的实例会较早被尝试。

-- You can change the order that type class instances are tried by
-- assigning them a _priority_. When an instance is declared, it is
-- assigned a default priority value. You can assign other priorities
-- when defining an instance. The following example illustrates how this
-- is done:
你可以通过为类型类实例分配 _优先级_ 来更改尝试它们的顺序。
声明实例时，会为其分配默认优先级值。定义实例时，你可以分配其他优先级。
以下示例说明了如何执行此操作：

```lean
class Foo where
  a : Nat
  b : Nat

instance (priority := default + 1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default + 2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl
```

-- # Coercions using Type Classes
# 使用类型类的强制转换
%%%
tag := "coercions-using-type-classes"
%%%

:::setup
```
variable {n : Nat} {α : Type u} {as : List α}
def Set (α : Type u) := α → Prop

```

-- The most basic type of coercion maps elements of one type to another. For example, a coercion from {lean}`Nat` to {lean}`Int` allows us to view any element {lean}`n : Nat` as an element of {lean}`Int`. But some coercions depend on parameters; for example, for any type {lean}`α`, we can view any element {lean}`as : List α` as an element of {lean}`Set α`, namely, the set of elements occurring in the list. The corresponding coercion is defined on the “family” of types {lean}`List α`, parameterized by {lean}`α`.
最基本的强制转换类型将一种类型的元素映射到另一种类型。
例如，从 {lean}`Nat` 到 {lean}`Int` 的强制转换允许我们将任何元素 {lean}`n : Nat` 视为 {lean}`Int` 的元素。
但有些强制转换取决于参数；例如，对于任何类型 {lean}`α`，我们可以将任何元素 {lean}`as : List α`
视为 {lean}`Set α` 的元素，即列表中出现的元素集合。
相应的强制转换定义在以 {lean}`α` 为参数的类型 “族” {lean}`List α` 上。
:::

-- Lean allows us to declare three kinds of coercions:
--
-- - from a family of types to another family of types
-- - from a family of types to the class of sorts
-- - from a family of types to the class of function types
--
-- The first kind of coercion allows us to view any element of a member of the source family as an element of a corresponding member of the target family. The second kind of coercion allows us to view any element of a member of the source family as a type. The third kind of coercion allows us to view any element of the source family as a function. Let us consider each of these in turn.
Lean 允许我们声明三种强制转换：

- 从一个类型族到另一个类型族
- 从一个类型族到 Sort 类
- 从一个类型族到函数类型类

第一种强制转换允许我们将源族成员的任何元素视为目标族相应成员的元素。
第二种强制转换允许我们将源族成员的任何元素视为类型。
第三种强制转换允许我们将源族的任何元素视为函数。让我们依次考虑这些。

:::setup
```
variable {α : Type u} {β : Type v} [Coe α β]
```

-- In Lean, coercions are implemented on top of the type class resolution framework. We define a coercion from {lean}`α` to {lean}`β` by declaring an instance of {lean}`Coe α β`. For example, we can define a coercion from {lean}`Bool` to {lean}`Prop` as follows:

在 Lean 中，强制转换是在类型类解析框架之上实现的。
我们通过声明 {lean}`Coe α β` 的实例来定义从 {lean}`α` 到 {lean}`β` 的强制转换。
例如，我们可以定义从 {lean}`Bool` 到 {lean}`Prop` 的强制转换如下：

```lean
instance : Coe Bool Prop where
  coe b := b = true
```
:::

-- This enables us to use boolean terms in {kw}`if`-{kw}`then`-{kw}`else` expressions:
这使我们能够在 {kw}`if`-{kw}`then`-{kw}`else` 表达式中使用布尔项：

```lean
#eval if true then 5 else 3

#eval if false then 5 else 3
```

:::leanFirst
-- We can define a coercion from {leanRef}`List α` to {leanRef}`Set α` as follows:
我们可以定义从 {leanRef}`List α` 到 {leanRef}`Set α` 的强制转换如下：

```lean
def Set (α : Type u) := α → Prop
def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
notation "{ " a " }" => Set.singleton a
infix:55 " ∪ " => Set.union
------
def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}

#check s ∪ [2, 3] -- s ∪ [2, 3].toSet : Set Nat
```
:::

-- We can use the notation {lit}`↑` to force a coercion to be introduced in a particular place. It is also helpful to make our intent clear, and work around limitations of the coercion resolution system.
我们可以使用符号 {lit}`↑` 来强制在特定位置引入强制转换。
这也有助于明确我们的意图，并绕过强制转换解析系统的限制。

```lean
def Set (α : Type u) := α → Prop
def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
notation "{ " a " }" => Set.singleton a
infix:55 " ∪ " => Set.union
def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet
instance : Coe (List α) (Set α) where
  coe a := a.toSet
------
def s : Set Nat := {1}

#check let x := ↑[2, 3]; s ∪ x -- let x := [2, 3].toSet; s ∪ x : Set Nat

#check let x := [2, 3]; s ∪ x -- let x := [2, 3]; s ∪ x.toSet : Set Nat
```


-- Lean also supports dependent coercions using the type class {lean}`CoeDep`. For example, we cannot coerce arbitrary propositions to {lean}`Bool`, only the ones that implement the {lean}`Decidable` typeclass.
Lean 还支持使用类型类 {lean}`CoeDep` 的依赖强制转换。
例如，我们不能将任意命题强制转换为 {lean}`Bool`，只能将实现了 {lean}`Decidable` 类型类的命题进行转换。

```lean
instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p
```

-- Lean will also chain (non-dependent) coercions as necessary. Actually, the type class {lean}`CoeT` is the transitive closure of {lean}`Coe`.
Lean 还会根据需要链接（非依赖）强制转换。实际上，类型类 {lean}`CoeT` 是 {lean}`Coe` 的传递闭包。

-- Let us now consider the second kind of coercion. By the _class of sorts_, we mean the collection of universes {lean}`Type u`. A coercion of the second kind is of the form:
现在让我们考虑第二种强制转换。所谓 _Sort 类_，我们指的是宇宙集合 {lean}`Type u`。第二种强制转换的形式如下：

```
    c : (x1 : A1) → ... → (xn : An) → F x1 ... xn → Type u
```

-- where {lit}`F` is a family of types as above. This allows us to write {lit}`s : t` whenever {lit}`t` is of type {lit}`F a₁ ... aₙ`. In other words, the coercion allows us to view the elements of {lit}`F a₁ ... aₙ` as types. This is very useful when defining algebraic structures in which one component, the carrier of the structure, is a {lean}`Type`. For example, we can define a semigroup as follows:
其中 {lit}`F` 是如上所述的类型族。这允许我们在 {lit}`t` 的类型为 {lit}`F a₁ ... aₙ` 时写出 {lit}`s : t`。
换句话说，强制转换允许我们将 {lit}`F a₁ ... aₙ` 的元素视为类型。
这在定义代数结构时非常有用，其中一个组件（结构的载体）是一个 {lean}`Type`。
例如，我们可以如下定义一个半群：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
```

:::setup

```
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b

variable {S : Semigroup} (a b : S.carrier)

instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
universe u
```
-- In other words, a semigroup consists of a type, {leanRef}`carrier`, and a multiplication, {leanRef}`mul`, with the property that the multiplication is associative. The {kw}`instance` command allows us to write {lean}`a * b` instead of {lean}`Semigroup.mul S a b` whenever we have {lean}`a b : S.carrier`; notice that Lean can infer the argument {leanRef}`S` from the types of {leanRef}`a` and {leanRef}`b`. The function {lean}`Semigroup.carrier` maps the class {leanRef}`Semigroup` to the sort {leanRef}`Type u`:
换句话说，一个半群由一个类型 {leanRef}`carrier` 和一个乘法 {leanRef}`mul` 组成，
且该乘法具有结合律。{kw}`instance` 命令允许我们在有 {lean}`a b : S.carrier` 时写出 {lean}`a * b`，
而不是 {lean}`Semigroup.mul S a b`；注意 Lean 可以从 {leanRef}`a` 和 {leanRef}`b` 的类型中推断出参数 {leanRef}`S`。
函数 {lean}`Semigroup.carrier` 将类 {leanRef}`Semigroup` 映射到 Sort {leanRef}`Type u`：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
------
#check Semigroup.carrier -- Semigroup.carrier.{u} (self : Semigroup) : Type u
```

-- If we declare this function to be a coercion, then whenever we have a semigroup {lean}`S : Semigroup`, we can write {lean}`a : S` instead of {lean}`a : S.carrier`:
如果我们声明此函数为强制转换，那么每当我们有一个半群 {lean}`S : Semigroup` 时，
我们就可以写出 {lean}`a : S` 而不是 {lean}`a : S.carrier`：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
------
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c
```

-- It is the coercion that makes it possible to write {leanRef}`(a b c : S)`. Note that, we define an instance of {leanRef}`CoeSort Semigroup (Type u)` instead of {lean}`Coe Semigroup (Type u)`.
正是强制转换使得写出 {leanRef}`(a b c : S)` 成为可能。注意，我们定义的是
{leanRef}`CoeSort Semigroup (Type u)` 的实例，而不是 {lean}`Coe Semigroup (Type u)`。

:::

::::setup
```
variable (B : Type u) (C : Type v)

```

-- By the _class of function types_, we mean the collection of Pi types {lean}`(z : B) → C`. The third kind of coercion has the form:

所谓 _函数类型类_，我们指的是 Pi 类型 {lean}`(z : B) → C` 的集合。
第三种强制转换的形式如下：

```
    c : (x₁ : A₁) → ... → (xₙ : Aₙ) → (y : F x₁ ... xₙ) → (z : B) → C
```

:::leanFirst
-- where {lit}`F` is again a family of types and {lit}`B` and {lit}`C` can depend on {lit}`x₁, ..., xₙ, y`. This makes it possible to write {lit}`t s` whenever {lit}`t` is an element of {lit}`F a₁ ... aₙ`. In other words, the coercion enables us to view elements of {lit}`F a₁ ... aₙ` as functions. Continuing the example above, we can define the notion of a morphism between semigroups {leanRef}`S1` and {leanRef}`S2`. That is, a function from the carrier of {leanRef}`S1` to the carrier of {leanRef}`S2` (note the implicit coercion) that respects the multiplication. The projection {leanRef}`Morphism.mor` takes a morphism to the underlying function:
其中 {lit}`F` 同样是一个类型族，而 {lit}`B` 和 {lit}`C` 可以取决于 {lit}`x₁, ..., xₙ, y`。
这使得在 {lit}`t` 是 {lit}`F a₁ ... aₙ` 的元素时写出 {lit}`t s` 成为可能。
换句话说，强制转换使我们能够将 {lit}`F a₁ ... aₙ` 的元素视为函数。
继续上面的例子，我们可以定义半群 {leanRef}`S1` 和 {leanRef}`S2` 之间态射（Morphism）的概念。
也就是说，从 {leanRef}`S1` 的载体到 {leanRef}`S2` 的载体的函数（注意隐式强制转换），且该函数遵守乘法。
投影 {leanRef}`Morphism.mor` 将态射映射到底层函数：


```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
------
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor
```
:::

-- As a result, it is a prime candidate for the third type of coercion.
因此，它是第三种强制转换的首选候选者。
::::

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)
------
instance (S1 S2 : Semigroup) :
    CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
        : f (a * b) = f a * f b :=
  f.resp_mul a b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [resp_mul f]
    _ = f a * f a * f a := by rw [resp_mul f]
```

-- With the coercion in place, we can write {leanRef}`f (a * a * a)` instead of {leanRef}`f.mor (a * a * a)`. When the {leanRef}`Morphism`, {leanRef}`f`, is used where a function is expected, Lean inserts the coercion. Similar to {lean}`CoeSort`, we have yet another class {lean}`CoeFun` for this class of coercions. The parameter {lit}`γ` is used to specify the function type we are coercing to. This type may depend on the type we are coercing from.
有了强制转换，我们就可以写出 {leanRef}`f (a * a * a)` 而不是 {leanRef}`f.mor (a * a * a)`。
当在需要函数的地方使用 {leanRef}`Morphism` {leanRef}`f` 时，Lean 会插入强制转换。
与 {lean}`CoeSort` 类似，我们还有另一个类 {lean}`CoeFun` 用于此类强制转换。
参数 {lit}`γ` 用于指定我们要强制转换到的函数类型。该类型可能取决于我们要强制转换的类型。
