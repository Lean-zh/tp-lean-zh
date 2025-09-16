<!--
# Type Classes
-->

# 类型类

<!--
Type classes were introduced as a principled way of enabling
ad-hoc polymorphism in functional programming languages. We first observe that it
would be easy to implement an ad-hoc polymorphic function (such as addition) if the
function simply took the type-specific implementation of addition as an argument
and then called that implementation on the remaining arguments. For example,
suppose we declare a structure in Lean to hold implementations of addition.
-->

将  **类型类（Type Class）**  作为一种原则性方法引入，
是为了在函数式编程语言中支持  **特设多态（Ad-hoc Polymorphism）** 。
我们首先观察到，如果函数简单地接受特定类型的实现作为参数，
然后在其余参数上调用该实现，则很容易实现特设多态函数（如加法）。
例如，假设我们在 Lean 中声明一个结构体来保存加法的实现：

```lean
# namespace Ex
structure Add (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → Add a → a → a → a
# end Ex
```

<!--
In the above Lean code, the field `add` has type
`Add.add : {a : Type} → Add a → a → a → a`
where the curly braces around the type `a` mean that it is an implicit argument.
We could implement `double` by:
-->

在上面 Lean 代码中，字段 `add` 的类型为 `Add.add : {a : Type} → Add a → a → a → a`
其中类型 `a` 周围的大括号表示它是一个隐式参数。我们可以通过以下方式实现 `double`：

```lean
# namespace Ex
# structure Add (a : Type) where
#  add : a → a → a
def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10
-- 100

#eval double { add := Int.add } 10
-- 20
# end Ex
```

<!--
Note that you can double a natural number `n` by `double { add := Nat.add } n`.
Of course, it would be highly cumbersome for users to manually pass the
implementations around in this way.
Indeed, it would defeat most of the potential benefits of ad-hoc
polymorphism.
-->

注意，你可以用 `double { add := Nat.add } n` 使一个自然数 `n` 翻倍。
当然，以这种方式让用户手动四处传递实现会非常繁琐。
实际上，这会消除掉特设多态的大部分潜在好处。

<!--
The main idea behind type classes is to make arguments such as `Add a` implicit,
and to use a database of user-defined instances to synthesize the desired instances
automatically through a process known as typeclass resolution. In Lean, by changing
`structure` to `class` in the example above, the type of `Add.add` becomes:
-->

类型类的主要思想是使诸如 `Add a` 之类的参数变为隐含的，
并使用用户定义实例的数据库通过称为类型类解析的过程自动合成所需的实例。
在 Lean 中，通过在以上示例中将 `structure` 更改为 `class`，`Add.add` 的类型会变为：

```lean
# namespace Ex
class Add (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → [self : Add a] → a → a → a
# end Ex
```

<!--
where the square brackets indicate that the argument of type `Add a` is *instance implicit*,
i.e. that it should be synthesized using typeclass resolution. This version of
`add` is the Lean analogue of the Haskell term `add :: Add a => a -> a -> a`.
Similarly, we can register instances by:
-->

其中方括号表示类型为 `Add a` 的参数是  **实例隐式的** ，
即，它应该使用类型类解析合成。这个版本的 `add` 是 Haskell 项
`add :: Add a => a -> a -> a` 的 Lean 类比。
同样，我们可以通过以下方式注册实例：

```lean
# namespace Ex
# class Add (a : Type) where
#  add : a → a → a
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add
# end Ex
```

<!--
Then for `n : Nat` and `m : Nat`, the term `Add.add n m` triggers typeclass resolution with
the goal of `Add Nat`, and typeclass resolution will synthesize the instance for `Nat` above.
We can now reimplement `double` using an instance implicit by:
-->

接着对于 `n : Nat` 和 `m : Nat`，项 `Add.add n m` 触发了类型类解析，
目标为 `Add Nat`，且类型类解析将综合上面 `Nat` 的实例。
现在，我们可以通过隐式的实例重新实现 `double` 了：

```lean
# namespace Ex
# class Add (a : Type) where
#   add : a → a → a
# instance : Add Nat where
#  add := Nat.add
# instance : Add Int where
#  add := Int.add
# instance : Add Float where
#  add := Float.add
def double [Add a] (x : a) : a :=
  Add.add x x

#check @double
-- @double : {a : Type} → [inst : Add a] → a → a

#eval double 10
-- 20

#eval double (10 : Int)
-- 100

#eval double (7 : Float)
-- 14.000000

#eval double (239.0 + 2)
-- 482.000000

# end Ex
```

<!--
In general, instances may depend on other instances in complicated ways. For example,
you can declare an (anonymous) instance stating that if `a` has addition, then `Array a`
has addition:
-->

一般情况下，实例可能以复杂的方式依赖于其他实例。例如，你可以声明一个（匿名）实例，
说明如果 `a` 存在加法，那么 `Array a` 也存在加法：

```lean
instance [Add a] : Add (Array a) where
  add x y := Array.zipWith (· + ·) x y

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

#eval #[1, 2] + #[3, 4]
-- #[4, 6]
```

<!--
Note that `(· + ·)` is notation for `fun x y => x + y` in Lean.
-->

请注意，`(· + ·)` 是 Lean 中 `fun x y => x + y` 的记法。

<!--
The example above demonstrates how type classes are used to overload notation.
Now, we explore another application. We often need an arbitrary element of a given type.
Recall that types may not have any elements in Lean.
It often happens that we would like a definition to return an arbitrary element in a "corner case."
For example, we may like the expression ``head xs`` to be of type ``a`` when ``xs`` is of type ``List a``.
Similarly, many theorems hold under the additional assumption that a type is not empty.
For example, if ``a`` is a type, ``exists x : a, x = x`` is true only if ``a`` is not empty.
The standard library defines a type class ``Inhabited`` to enable type class inference to infer a
"default" element of an inhabited type.
Let us start with the first step of the program above, declaring an appropriate class:
-->

上述示例演示了类型类如何用于重载符号。现在，我们探索另一个应用程序。
我们经常需要给定类型的任意元素。回想一下类型在 Lean 中可能没有任何元素。
我们经常希望在一个「边界情况」下定义返回一个任意元素。
例如，我们可能希望当 ``xs`` 为 ``List a`` 类型时 ``head xs`` 表达式的类型为 ``a``。
类似地，许多定理在类型不为空的附加假设下成立。例如，如果 ``a`` 是一个类型，
则 ``exists x : a, x = x`` 仅在 ``a`` 不为空时为真。标准库定义了一个类型类
``Inhabited``，它能够让类型类推理来推断 **可居（Inhabited）** 类型类的「默认」元素。
让我们从上述程序的第一步开始，声明一个适当的类：

```lean
# namespace Ex
class Inhabited (a : Type u) where
  default : a

#check @Inhabited.default
-- Inhabited.default : {a : Type u} → [self : Inhabited a] → a
# end Ex
```

<!--
Note `Inhabited.default` doesn't have any explicit arguments.
-->

注意 `Inhabited.default` 没有任何显式参数。

<!--
An element of the class ``Inhabited a`` is simply an expression of the form ``Inhabited.mk x``, for some element ``x : a``.
The projection ``Inhabited.default`` will allow us to "extract" such an element of ``a`` from an element of ``Inhabited a``.
Now we populate the class with some instances:
-->

类 ``Inhabited a`` 的某个元素只是形式为 ``Inhabited.mk x`` 的表达式，
其中 ``x : a`` 为某个元素。投影 ``Inhabited.default`` 可让我们从 ``Inhabited a``
的某个元素中「提取」出 ``a`` 的某个元素。现在我们用一些实例填充该类：

```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- 0

#eval (Inhabited.default : Bool)
-- true
# end Ex
```

<!--
You can use the command `export` to create the alias `default` for `Inhabited.default`
-->
你可以用 `export` 命令来为 `Inhabited.default` 创建别名 `default`

```lean
# namespace Ex
# class Inhabited (a : Type _) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# instance : Inhabited Unit where
#  default := ()
# instance : Inhabited Prop where
#  default := True
export Inhabited (default)

#eval (default : Nat)
-- 0

#eval (default : Bool)
-- true
# end Ex
```

<!--
## Chaining Instances
-->

## 链接实例

<!--
If that were the extent of type class inference, it would not be all that impressive;
it would be simply a mechanism of storing a list of instances for the elaborator to find in a lookup table.
What makes type class inference powerful is that one can *chain* instances. That is,
an instance declaration can in turn depend on an implicit instance of a type class.
This causes class inference to chain through instances recursively, backtracking when necessary, in a Prolog-like search.
-->

以类型类推断的层面来看，它并不那么令人印象深刻；
它不过是一种为精细器存储实例列表的机制，用于在查询表中查找。
类型类推断变得强大的原因在于，它能够「链接（Chain）」实例。也就是说，
实例声明本身可以依赖类型类的隐式实例。
这导致类推断递归地通过实例进行链接，并在必要时回溯，就像 Prolog 中的搜索一样。

<!--
For example, the following definition shows that if two types ``a`` and ``b`` are inhabited, then so is their product:
-->
-->

例如，以下定义展示了若两个类型 ``a`` 和 ``b`` 包含元素，则二者的积也包含元素：

```lean
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)
```

<!--
With this added to the earlier instance declarations, type class instance can infer, for example, a default element of ``Nat × Bool``:
-->

将它添加到先前的实例声明后，类型类实例就能推导了，例如 ``Nat × Bool`` 的默认元素为：

```lean
# namespace Ex
# class Inhabited (a : Type u) where
#  default : a
# instance : Inhabited Bool where
#  default := true
# instance : Inhabited Nat where
#  default := 0
# opaque default [Inhabited a] : a :=
#  Inhabited.default
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)
-- (0, true)
# end Ex
```

<!--
Similarly, we can inhabit type function with suitable constant functions:
-->

与此类似，我们可以使用合适的常量函数使其居留到类型函数中：

```lean
instance [Inhabited b] : Inhabited (a → b) where
  default := fun _ => default
```

<!--
As an exercise, try defining default instances for other types, such as `List` and `Sum` types.
-->

作为练习，请尝试为其他类型定义默认实例，例如 `List` 和 `Sum` 类型。

<!--
The Lean standard library contains the definition `inferInstance`. It has type `{α : Sort u} → [i : α] → α`,
and is useful for triggering the type class resolution procedure when the expected type is an instance.
-->

Lean 标准库包含了定义 `inferInstance`，它的类型为 `{α : Sort u} → [i : α] → α`，
它在期望的类型是一个实例时触发类型类解析过程十分有用。

```lean
#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

theorem ex : foo.default = (default, default) :=
  rfl
```

<!--
You can use the command `#print` to inspect how simple `inferInstance` is.
-->

<!--
You can use the command `#print` to inspect how simple `inferInstance` is.
-->

你可以使用命令 `#print` 来检查 `inferInstance` 有多简单。

```lean
#print inferInstance
```

<!--
## ToString
-->

## ToString 方法

<!--
The polymorphic method `toString` has type `{α : Type u} → [ToString α] → α → String`. You implement the instance
for your own types and use chaining to convert complex values into strings. Lean comes with `ToString` instances
for most builtin types.
-->

多态方法 `toString` 类型为 `{α : Type u} → [ToString α] → α → String`。
你可以为自己的类型实现实例并使用链接将复杂的值转换为字符串。
Lean 为大多数内置类型都提供了 `ToString` 实例。

```lean
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")
```

<!--
## Numerals
-->

## 数值

<!--
Numerals are polymorphic in Lean. You can use a numeral (e.g., `2`) to denote an element of any type that implements
the type class `OfNat`.
-->

数值在 Lean 中是多态的。你可以用一个数值（例如 `2`）来表示任何实现了类型类
`OfNat` 的类型中的一个元素。

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

#check (2 : Rational) -- Rational
#check (2 : Nat)      -- Nat
```

<!--
Lean elaborates the terms `(2 : Nat)` and `(2 : Rational)` as
`OfNat.ofNat Nat 2 (instOfNatNat 2)` and
`OfNat.ofNat Rational 2 (instOfNatRational 2)` respectively.
We say the numerals `2` occurring in the elaborated terms are *raw* natural numbers.
You can input the raw natural number `2` using the macro `nat_lit 2`.
-->

<!--
Lean elaborates the terms `(2 : Nat)` and `(2 : Rational)` as
`OfNat.ofNat Nat 2 (instOfNatNat 2)` and
`OfNat.ofNat Rational 2 (instOfNatRational 2)` respectively.
We say the numerals `2` occurring in the elaborated terms are *raw* natural numbers.
You can input the raw natural number `2` using the macro `nat_lit 2`.
-->

Lean 会将项 `(2 : Nat)` 和 `(2 : Rational)` 分别繁饰（Elaborate）为：
`OfNat.ofNat Nat 2 (instOfNatNat 2)` 和
`OfNat.ofNat Rational 2 (instOfNatRational 2)`。
我们将繁饰的项中出现的数字 `2` 称为  **原始**  自然数。
你可以使用宏 `nat_lit 2` 来输入原始自然数 `2`。

```lean
#check nat_lit 2  -- Nat
```

<!--
Raw natural numbers are *not* polymorphic.
-->

原始自然数  **不是**  多态的。

<!--
The `OfNat` instance is parametric on the numeral. So, you can define instances for particular numerals.
The second argument is often a variable as in the example above, or a *raw* natural number.
-->

`OfNat` 实例对数值进行了参数化，因此你可以定义特定数字的实例。
第二个参数通常是变量，如上例所示，或者是一个  **原始**  自然数。

```lean
class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1
```

<!--
## Output Parameters
-->

## 输出参数

<!--
By default, Lean only tries to synthesize an instance `Inhabited T` when the term `T` is known and does not
contain missing parts. The following command produces the error
"typeclass instance problem is stuck, it is often due to metavariables `?m.7`" because the type has a missing part (i.e., the `_`).
-->

默认情况下，Lean 仅当项 `T` 已知时且不包含缺失部分时，会尝试合成实例 `Inhabited T`。
以下命令会产生错「typeclass instance problem is stuck, it is often due to metavariables `?m.7`
（类型类实例问题卡住了，通常是由于元变量 `?m.7` 引起的）」因为该类型有缺失的部分（即 `_`）。

```lean
#check_failure (inferInstance : Inhabited (Nat × _))
```

<!--
You can view the parameter of the type class `Inhabited` as an *input* value for the type class synthesizer.
When a type class has multiple parameters, you can mark some of them as output parameters.
Lean will start type class synthesizer even when these parameters have missing parts.
In the following example, we use output parameters to define a *heterogeneous* polymorphic
multiplication.
-->

你可以将类型类 `Inhabited` 的参数视为类型类合成器的  **输入**  值。
当类型类有多个参数时，可以将其中一些标记为输出参数。
即使这些参数有缺失部分，Lean 也会开始类型类合成。
在下面的示例中，我们使用输出参数定义一个  **异质（Heterogeneous）**  的多态乘法。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12
#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
# end Ex
```

<!--
The parameters `α` and `β` are considered input parameters and `γ` an output one.
Given an application `hMul a b`, after the types of `a` and `b` are known, the type class
synthesizer is invoked, and the resulting type is obtained from the output parameter `γ`.
In the example above, we defined two instances. The first one is the homogeneous
multiplication for natural numbers. The second is the scalar multiplication for arrays.
Note that you chain instances and generalize the second instance.
-->

参数 `α` 和 `β` 会被视为输入参数，`γ` 被视为输出参数。
如果给定一个应用 `hMul a b`，那么在知道 `a` 和 `b` 的类型后，
将调用类型类合成器，并且可以从输出参数 `γ` 中获得最终的类型。
在上文中的示例中，我们定义了两个实例。第一个实例是针对自然数的同质乘法。
第二个实例是针对数组的标量乘法。请注意，你可以链接实例，并推广第二个实例。

```lean
# namespace Ex
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
# end Ex
```

<!--
You can use our new scalar array multiplication instance on arrays of type `Array β`
with a scalar of type `α` whenever you have an instance `HMul α β γ`.
In the last `#eval`, note that the instance was used twice on an array of arrays.
-->

当你拥有 `HMul α β γ` 的实例时，可以在类型为 `Array β` 的数组上将其使用标量类型
`α` 的新标量数组乘法实例。在最后的 `#eval` 中，请注意该实例曾在数组数组中使用了两次。

<!--
## Default Instances
-->

## Default Instances

<!--
In the class `HMul`, the parameters `α` and `β` are treated as input values.
Thus, type class synthesis only starts after these two types are known. This may often
be too restrictive.
-->

在类 `HMul` 中，参数 `α` 和 `β` 被当做输入值。
因此，类型类合成仅在已知这两种类型时才开始。这通常可能过于严格。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

-- Error "typeclass instance problem is stuck, it is often due to metavariables HMul ?m.89 ?m.90 ?m.91"
#check_failure fun y => xs.map (fun x => hMul x y)
# end Ex
```

<!--
The instance `HMul` is not synthesized by Lean because the type of `y` has not been provided.
However, it is natural to assume that the type of `y` and `x` should be the same in
this kind of situation. We can achieve exactly that using *default instances*.
-->

实例 `HMul` 没有被 Lean 合成，因为没有提供 `y` 的类型。
然而，在这种情况下，自然应该认为 `y` 和 `x` 的类型应该相同。
我们可以使用  **默认实例**  来实现这一点。

```lean
# namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)  -- Int → List Int
# end Ex
```

<!--
By tagging the instance above with the attribute `default_instance`, we are instructing Lean
to use this instance on pending type class synthesis problems.
The actual Lean implementation defines homogeneous and heterogeneous classes for arithmetical operators.
Moreover, `a+b`, `a*b`, `a-b`, `a/b`, and `a%b` are notations for the heterogeneous versions.
The instance `OfNat Nat n` is the default instance (with priority 100) for the `OfNat` class. This is why the numeral
`2` has type `Nat` when the expected type is not known. You can define default instances with higher
priority to override the builtin ones.
-->

通过给上述实例添加 `default_instance` 属性，我们指示 Lean 在挂起的类型类合成问题中使用此实例。
实际的 Lean 实现为算术运算符定义了同质和异质类。此外，`a+b`、`a*b`、`a-b`、`a/b` 和 `a%b`
是异质版本的记法。实例 `OfNat Nat n` 是 `OfNat` 类的默认实例（优先级 100）。
这就是当预期类型未知时，数字 `2` 具有类型 `Nat` 的原因。
你可以定义具有更高优先级的默认实例来覆盖内置实例。

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

#check 2 -- Rational
```

<!--
Priorities are also useful to control the interaction between different default instances.
For example, suppose `xs` has type `List α`. When elaborating `xs.map (fun x => 2 * x)`, we want the homogeneous instance for multiplication
to have higher priority than the default instance for `OfNat`. This is particularly important when we have implemented only the instance
`HMul α α α`, and did not implement `HMul Nat α α`.
Now, we reveal how the notation `a*b` is defined in Lean.
-->

优先级也适用于控制不同默认实例之间的交互。例如，假设 `xs` 有类型 `List α`。
在繁饰 `xs.map (fun x => 2 * x)` 时，我们希望乘法的同质实例比 `OfNat`
的默认实例具有更高的优先级。当我们仅实现了实例 `HMul α α α`，而未实现 `HMul Nat α α` 时，
这一点尤为重要。现在，我们展示了 `a*b` 记法在 Lean 中是如何定义的。

```lean
# namespace Ex
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
# end Ex
```

<!--
The `Mul` class is convenient for types that only implement the homogeneous multiplication.
-->

`Mul` 类是仅实现了同质乘法的类型的简便记法。

<!--
## Local Instances
-->

## 局部实例

<!--
Type classes are implemented using attributes in Lean. Thus, you can
use the `local` modifier to indicate that they only have effect until
the current ``section`` or ``namespace`` is closed, or until the end
of the current file.
-->

类型类是使用 Lean 中的属性（Attribute）来实现的。因此，你可以使用 `local`
修饰符表明它们只对当前 ``section`` 或 ``namespace`` 关闭之前或当前文件结束之前有效。

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

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance
```

<!--
You can also temporarily disable an instance using the `attribute` command
until the current ``section`` or ``namespace`` is closed, or until the end
of the current file.
-->

你也可使用 `attribute` 命令暂时禁用一个实例，直至当前的 ``section`` 或
``namespace`` 关闭，或直到当前文件的结尾。

```lean
structure Point where
  x : Nat
  y : Nat

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

attribute [-instance] addPoint

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance
```

<!--
We recommend you only use this command to diagnose problems.
-->

我们建议你只使用此命令来诊断问题。

<!--
## Scoped Instances
-->

## 作用于实例

<!--
You can also declare scoped instances in namespaces. This kind of instance is
only active when you are inside of the namespace or open the namespace.
-->

<!--
You can also declare scoped instances in namespaces. This kind of instance is
only active when you are inside of the namespace or open the namespace.
-->

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

-- #check fun (p : Point) => p + p + p  -- Error

namespace Point
-- instance `Add Point` is active again
#check fun (p : Point) => p + p + p

end Point

open Point -- activates instance `Add Point`
#check fun (p : Point) => p + p + p
```

<!--
You can use the command `open scoped <namespace>` to activate scoped attributes but will
not "open" the names from the namespace.
-->

<!--
You can use the command `open scoped <namespace>` to activate scoped attributes but will
not "open" the names from the namespace.
-->

你可以使用 `open scoped <namespace>` 命令来激活作用于内的属性，但不会「打开」名称空间中的名称。

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

-- #check fun (p : Point) => double p -- Error: unknown identifier 'double'
```

<!--
## Decidable Propositions
-->

## 可判定的命题

<!--
Let us consider another example of a type class defined in the
standard library, namely the type class of ``Decidable``
propositions. Roughly speaking, an element of ``Prop`` is said to be
decidable if we can decide whether it is true or false. The
distinction is only useful in constructive mathematics; classically,
every proposition is decidable. But if we use the classical principle,
say, to define a function by cases, that function will not be
computable. Algorithmically speaking, the ``Decidable`` type class can
be used to infer a procedure that effectively determines whether or
not the proposition is true. As a result, the type class supports such
computational definitions when they are possible while at the same
time allowing a smooth transition to the use of classical definitions
and classical reasoning.
-->

让我们考虑标准库中定义的另一个类型类，名为 ``Decidable`` 类型类。
粗略地讲，对于 ``Prop`` 的一个元素，如果我们可以判定它是真或假，它就被称为可判定的。
这种区别只有在构造性数学中才有用；在经典数学中，每个命题都是可判定的。
但如果我们使用经典原则，比如通过情况来定义一个函数，那么这个函数将不可计算。
从算法上来讲，``Decidable`` 类型类可以用来推导出一个过程，它能有效判定命题是否为真。
因此，该类型类支持这样的计算性定义（如果它们是可能的），
同时还允许平滑地过渡到经典定义和经典推理的使用。

<!--
In the standard library, ``Decidable`` is defined formally as follows:
-->

在标准库中，``Decidable`` 的形式化定义如下：

```lean
# namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
# end Hidden
```

<!--
Logically speaking, having an element ``t : Decidable p`` is stronger
than having an element ``t : p ∨ ¬p``; it enables us to define values
of an arbitrary type depending on the truth value of ``p``. For
example, for the expression ``if p then a else b`` to make sense, we
need to know that ``p`` is decidable. That expression is syntactic
sugar for ``ite p a b``, where ``ite`` is defined as follows:
-->

从逻辑上讲，拥有一个元素 ``t : Decidable p`` 比拥有一个元素 ``t : p ∨ ¬p`` 更强；
它允许我们定义一个任意类型的的值，这些值取决于 ``p`` 的真值。
例如，为了使表达式 ``if p then a else b`` 有意义，我们需要知道 ``p``
是可判定的。该表达式是 ``ite p a b`` 的语法糖，其中 ``ite`` 的定义如下：

```lean
# namespace Hidden
def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)
# end Hidden
```

<!--
The standard library also contains a variant of ``ite`` called
``dite``, the dependent if-then-else expression. It is defined as
follows:
-->

<!--
The standard library also contains a variant of ``ite`` called
``dite``, the dependent if-then-else expression. It is defined as
follows:
-->

标准库中还包含 ``ite`` 的一种变体，称为 ``dite``，
即依赖 if-then-else 表达式。它的定义如下：

```lean
# namespace Hidden
def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
# end Hidden
```

<!--
That is, in ``dite c t e``, we can assume ``hc : c`` in the "then"
branch, and ``hnc : ¬ c`` in the "else" branch. To make ``dite`` more
convenient to use, Lean allows us to write ``if h : c then t else e``
instead of ``dite c (λ h : c => t) (λ h : ¬ c => e)``.
-->

即在 ``dite c t e`` 表达式中，我们可以在 ``then`` 分支假定
``hc : c``，在 ``else`` 分支假定 ``hnc : ¬ c``。为了方便 ``dite`` 的使用，
Lean 允许我们将 ``if h : c then t else e`` 写作 ``dite c (λ h : c => t) (λ h : ¬ c => e)``。

<!--
Without classical logic, we cannot prove that every proposition is
decidable. But we can prove that *certain* propositions are
decidable. For example, we can prove the decidability of basic
operations like equality and comparisons on the natural numbers and
the integers. Moreover, decidability is preserved under propositional
connectives:
-->

如果没有经典逻辑，我们就不能证明每个命题都是可判定的。
但我们可以证明 **某些** 命题是可判定的。
例如，我们可以证明基本运算（比如自然数和整数上的等式和比较）的可判定性。
此外，命题连词下的可判定性被保留了下来：

```lean
#check @instDecidableAnd
  -- {p q : Prop} → [Decidable p] → [Decidable q] → Decidable (And p q)

#check @instDecidableOr
#check @instDecidableNot
```

<!--
Thus we can carry out definitions by cases on decidable predicates on
the natural numbers:
-->

因此我们可以按照自然数上的可判定谓词的情况给出定义：

```lean
def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true
#print step
```

<!--
Turning on implicit arguments shows that the elaborator has inferred
the decidability of the proposition ``x < a ∨ x > b``, simply by
applying appropriate instances.
-->

打开隐式参数显示，繁饰器已经推断出了命题 ``x < a ∨ x > b`` 的可判定性，
只需应用适当的实例即可。

<!--
With the classical axioms, we can prove that every proposition is
decidable. You can import the classical axioms and make the generic
instance of decidability available by opening the `Classical` namespace.
-->

使用经典公理，我们可以证明每个命题都是可判定的。
你可以导入经典公理，并通过打开 `Classical` 命名空间来提供可判定的通用实例。

```lean
open Classical
```

<!--
Thereafter ``Decidable p`` has an instance for every ``p``.
Thus all theorems in the library
that rely on decidability assumptions are freely available when you
want to reason classically. In [Chapter Axioms and Computation](./axioms_and_computation.md),
we will see that using the law of the
excluded middle to define functions can prevent them from being used
computationally. Thus, the standard library assigns a low priority to
the `propDecidable` instance.
-->

之后 ``Decidable p`` 就会拥有任何 ``p`` 的实例。
因此，当你想进行经典推理时，库中的所有依赖于可判定假设的定理都会免费提供。
在[公理和计算](./axioms_and_computation.md)一章中，
我们将看到，使用排中律来定义函数会阻止它们被计算性地使用。
因此，标准库将 ``propDecidable`` 实例的优先级设为低。

```lean
# namespace Hidden
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
# end Hidden
```

<!--
This guarantees that Lean will favor other instances and fall back on
``propDecidable`` only after other attempts to infer decidability have
failed.
-->

这能保证 Lean 会优先采用其他实例，只有在推断可判定性失败后才退回到 ``propDecidable``。

<!--
The ``Decidable`` type class also provides a bit of small-scale
automation for proving theorems. The standard library introduces the
tactic `decide` that uses the `Decidable` instance to solve simple goals.
-->

``Decidable`` 类型类还为定理证明提供了一点小规模的自动化。
标准库引入了使用 ``Decidable`` 实例解决简单目标的策略 ``decide``。

```lean
example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬ (True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1+1 := by
  decide

#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (Eq.refl true)

#check @of_decide_eq_true
-- ∀ {p : Prop} [Decidable p], decide p = true → p

#check @decide
-- (p : Prop) → [Decidable p] → Bool
```

<!--
They work as follows. The expression ``decide p`` tries to infer a
decision procedure for ``p``, and, if it is successful, evaluates to
either ``true`` or ``false``. In particular, if ``p`` is a true closed
expression, ``decide p`` will reduce definitionally to the Boolean ``true``.
On the assumption that ``decide p = true`` holds, ``of_decide_eq_true``
produces a proof of ``p``. The tactic ``decide`` puts it all together to
prove a target ``p``. By the previous observations,
``decide`` will succeed any time the inferred decision procedure
 for ``c`` has enough information to evaluate, definitionally, to the ``isTrue`` case.
-->

它们的工作方式如下：表达式 ``decide p`` 尝试推断 ``p`` 的决策过程，如果成功，
则会求值为 ``true`` 或 ``false``。特别是，如果 ``p`` 是一个为真的封闭表达式，
``decide p`` 将根据定义化简未为布尔值 ``true``。在假设 ``decide p = true``
成立的情况下，``of_decide_eq_true`` 会生成 ``p`` 的证明。
策略 ``decide`` 将所有这些组合在一起以证明目标 ``p``。根据前面的观察，
只要推断出的决策过程拥有足够的信息，可以根据定义将 ``c`` 求值为 ``isTrue`` 的情况，
那么 ``decide`` 就会成功。

<!--
## Managing Type Class Inference
-->

## 类型类推断的管理

<!--
If you are ever in a situation where you need to supply an expression
that Lean can infer by type class inference, you can ask Lean to carry
out the inference using `inferInstance`:
-->

如果你需要使用类型类推断来提供一个 Lean 可以推断的表达式，
那么你可以使用 `inferInstance` 让 Lean 执行推断：

```lean
def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance
-- {α : Sort u} → [α] → α
```

<!--
In fact, you can use Lean's ``(t : T)`` notation to specify the class whose instance you are looking for,
in a concise manner:
-->

你可以使用 Lean 中的 ``(t : T)`` 语法指定你正在寻找的类的实例，
这是一种很简洁的方式：

```lean
#check (inferInstance : Add Nat)
```

<!--
You can also use the auxiliary definition `inferInstanceAs`:
-->

你也可以使用辅助定义 `inferInstanceAs`：

```lean
#check inferInstanceAs (Add Nat)

#check @inferInstanceAs
-- (α : Sort u) → [α] → α
```

<!--
Sometimes Lean can't find an instance because the class is buried
under a definition. For example, Lean cannot
find an instance of ``Inhabited (Set α)``. We can declare one
explicitly:
-->

有时 Lean 会找不到一个实例，因为该类被定义所掩盖。例如，Lean 无法
找到 ``Inhabited (Set α)`` 的一个实例。我们可以显式地声明一个：

```lean
def Set (α : Type u) := α → Prop

-- fails
-- example : Inhabited (Set α) :=
--  inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))
```

<!--
At times, you may find that the type class inference fails to find an
expected instance, or, worse, falls into an infinite loop and times
out. To help debug in these situations, Lean enables you to request a
trace of the search:
-->

有时，你可能会发现类型类推断未找到预期的实例，或者更糟的是，陷入无限循环并超时。
为了在这些情况下帮助调试，Lean 可以让你请求搜索的跟踪：

```lean
set_option trace.Meta.synthInstance true
```

<!--
If you are using VS Code, you can read the results by hovering over
the relevant theorem or definition, or opening the messages window
with ``Ctrl-Shift-Enter``. In Emacs, you can use ``C-c C-x`` to run an
independent Lean process on your file, and the output buffer will show
a trace every time the type class resolution procedure is subsequently
triggered.
-->

如果你使用的是 VS Code，可以通过将鼠标悬停在相关的定理或定义上，
或按 ``Ctrl-Shift-Enter`` 打开消息窗口来阅读结果。在 Emacs 中，
你可以使用 ``C-c C-x`` 在你的文件中运行一个独立的 Lean 进程，
并且在每次触发类型类解析过程时，输出缓冲区都会显示一个跟踪。

<!--
You can also limit the search using the following options:
-->

使用以下选项，你还可以限制搜索：

```lean
set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
```

<!--
Option `synthInstance.maxHeartbeats` specifies the maximum amount of
heartbeats per typeclass resolution problem. A heartbeat is the number of
(small) memory allocations (in thousands), 0 means there is no limit.
Option `synthInstance.maxSize` is the maximum number of instances used
to construct a solution in the type class instance synthesis procedure.
-->

选项 `synthInstance.maxHeartbeats` 指定每个类型类解析问题可能出现的心跳（Heartbeat）次数上限。
心跳是（小）内存分配的次数（以千为单位），0 表示没有上限。
选项 `synthInstance.maxSize` 是用于构建类型类实例合成过程中解的实例个数。

<!--
Remember also that in both the VS Code and Emacs editor modes, tab
completion works in ``set_option``, to help you find suitable options.
-->

另外请记住，在 VS Code 和 Emacs 编辑器模式中，制表符补全也可用于
``set_option``，它可以帮助你查找合适的选项。

<!--
As noted above, the type class instances in a given context represent
a Prolog-like program, which gives rise to a backtracking search. Both
the efficiency of the program and the solutions that are found can
depend on the order in which the system tries the instance. Instances
which are declared last are tried first. Moreover, if instances are
declared in other modules, the order in which they are tried depends
on the order in which namespaces are opened. Instances declared in
namespaces which are opened later are tried earlier.
-->

如上所述，给定语境中的类型类实例代表一个类似 Prolog 的程序，它会进行回溯搜索。
同时程序的效率和找到的解都取决于系统尝试实例的顺序。最后声明的实例首先尝试。
此外，如果在其它模块中声明了实例，它们尝试的顺序取决于打开名称空间的顺序。
在后面打开的名称空间中声明的实例，会更早尝试。

<!--
You can change the order that type class instances are tried by
assigning them a *priority*. When an instance is declared, it is
assigned a default priority value. You can assign other priorities
when defining an instance. The following example illustrates how this
is done:
-->

你可以按对类型类实例进行尝试的顺序来更改这些实例，
方法是为它们分配一个 **优先级** 。在声明实例时，
它将被分配一个默认优先级值。在定义实例时，你可以分配其他的优先级。
以下示例说明了如何执行此操作：

```lean
class Foo where
  a : Nat
  b : Nat

instance (priority := default+1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default+2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl
```

<!--
## Coercions using Type Classes
-->

## 使用类型泛型进行强制转换

<!--
The most basic type of coercion maps elements of one type to another. For example, a coercion from ``Nat`` to ``Int`` allows us to view any element ``n : Nat`` as an element of ``Int``. But some coercions depend on parameters; for example, for any type ``α``, we can view any element ``as : List α`` as an element of ``Set α``, namely, the set of elements occurring in the list. The corresponding coercion is defined on the "family" of types ``List α``, parameterized by ``α``.
-->

最基本的强制转换将一种类型的元素映射到另一种类型。
例如，从 ``Nat`` 到 ``Int`` 的强制转换允许我们将任何元素 ``n : Nat`` 视作元素 ``Int``。
但一些强制转换依赖于参数；例如，对于任何类型 ``α``，我们可以将任何元素
``as : List α`` 视为 ``Set α`` 的元素，即，列表中出现的元素组成的集合。
相应的强制转换被定义在 ``List α`` 的「类型族（Type Family）」上，由 ``α`` 参数化。

<!--
Lean allows us to declare three kinds of coercions:

- from a family of types to another family of types
- from a family of types to the class of sorts
- from a family of types to the class of function types
-->

Lean 允许我们声明三类强制转换：

- 从一个类型族到另一个类型族
- 从一个类型族到种类（Sort）的类
- 从一个类型族到函数类型的类

<!--
The first kind of coercion allows us to view any element of a member of the source family as an element of a corresponding member of the target family. The second kind of coercion allows us to view any element of a member of the source family as a type. The third kind of coercion allows us to view any element of the source family as a function. Let us consider each of these in turn.
-->

第一种强制转换允许我们将源类型族任何成员的元素视为目标类型族中对应成员的元素。
第二种强制转换允许我们将源类型族任何成员的元素视为类型。
第三种强制转换允许我们将源类型族任何成员的元素视为函数。
让我们逐一考虑这些。

<!--
In Lean, coercions are implemented on top of the type class resolution framework. We define a coercion from ``α`` to ``β`` by declaring an instance of ``Coe α β``. For example, we can define a coercion from ``Bool`` to ``Prop`` as follows:
-->

在 Lean 中，强制转换在类型类解析框架的基础上实现。我们通过声明 ``Coe α β`` 的实例，
定义从 ``α`` 到 ``β`` 的强制转换。例如，以下内容可以定义从 ``Bool`` 到 ``Prop`` 的强制转换：

```lean
instance : Coe Bool Prop where
  coe b := b = true
```

<!--
This enables us to use boolean terms in if-then-else expressions:
-->

这使得我们可以在 if-then-else 表达式中使用布尔项：

```lean
#eval if true then 5 else 3
#eval if false then 5 else 3
```

<!--
We can define a coercion from ``List α`` to ``Set α`` as follows:
-->

我们可以定义一个从 ``List α`` 到 ``Set α`` 的强制转换，如下所示：

```lean
# def Set (α : Type u) := α → Prop
# def Set.empty {α : Type u} : Set α := fun _ => False
# def Set.mem (a : α) (s : Set α) : Prop := s a
# def Set.singleton (a : α) : Set α := fun x => x = a
# def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
# notation "{ " a " }" => Set.singleton a
# infix:55 " ∪ " => Set.union
def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}
#check s ∪ [2, 3]
-- s ∪ List.toSet [2, 3] : Set Nat
```

<!--
We can use the notation ``↑`` to force a coercion to be introduced in a particular place. It is also helpful to make our intent clear, and work around limitations of the coercion resolution system.
-->

我们可以使用符号 ``↑`` 在特定位置强制引入强制转换。
这也有助于明确我们的意图，并解决强制转换解析系统中的限制。

```lean
# def Set (α : Type u) := α → Prop
# def Set.empty {α : Type u} : Set α := fun _ => False
# def Set.mem (a : α) (s : Set α) : Prop := s a
# def Set.singleton (a : α) : Set α := fun x => x = a
# def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
# notation "{ " a " }" => Set.singleton a
# infix:55 " ∪ " => Set.union
# def List.toSet : List α → Set α
#   | []    => Set.empty
#   | a::as => {a} ∪ as.toSet
# instance : Coe (List α) (Set α) where
#   coe a := a.toSet
def s : Set Nat := {1}

#check let x := ↑[2, 3]; s ∪ x
-- let x := List.toSet [2, 3]; s ∪ x : Set Nat
#check let x := [2, 3]; s ∪ x
-- let x := [2, 3]; s ∪ List.toSet x : Set Nat
```

<!--
Lean also supports dependent coercions using the type class `CoeDep`. For example, we cannot coerce arbitrary propositions to `Bool`, only the ones that implement the `Decidable` typeclass.
-->

Lean 还使用类型类 `CoeDep` 支持依值类型强制转换。
例如，我们无法将任意命题强制转换到 `Bool`，只能转换实现了 `Decidable` 类型类的命题。

```lean
instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p
```

<!--
Lean will also chain (non-dependent) coercions as necessary. Actually, the type class ``CoeT`` is the transitive closure of ``Coe``.
-->

Lean 也会在有需要的时候构造链式（非依赖的）强制转换。事实上，类型类 ``CoeT`` 是 ``Coe`` 的传递闭包。

<!--
Let us now consider the second kind of coercion. By the *class of sorts*, we mean the collection of universes ``Type u``. A coercion of the second kind is of the form:
-->

现在我们来考查第二种强制转换。 **种类类（Class of Sort）** 是指宇宙 ``Type u`` 的集合。
第二种强制转换的形式如下：

```
    c : (x1 : A1) → ... → (xn : An) → F x1 ... xn → Type u
```

<!--
where ``F`` is a family of types as above. This allows us to write ``s : t`` whenever ``t`` is of type ``F a1 ... an``. In other words, the coercion allows us to view the elements of ``F a1 ... an`` as types. This is very useful when defining algebraic structures in which one component, the carrier of the structure, is a ``Type``. For example, we can define a semigroup as follows:
-->

其中 ``F`` 是如上所示的一族类型。这允许我们当 ``t`` 的类型为 ``F a1 ... an`` 时编写 ``s : t`` 。
换言之，类型转换允许我们将 ``F a1 ... an`` 的元素视为类型。
这在定义代数结构时非常有用，其中一个组成部分（即结构的载体）为 ``Type``。
例如，我们可以按以下方式定义一个半群：

```lean
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
```

<!--
In other words, a semigroup consists of a type, ``carrier``, and a multiplication, ``mul``, with the property that the multiplication is associative. The ``instance`` command allows us to write ``a * b`` instead of ``Semigroup.mul S a b`` whenever we have ``a b : S.carrier``; notice that Lean can infer the argument ``S`` from the types of ``a`` and ``b``. The function ``Semigroup.carrier`` maps the class ``Semigroup`` to the sort ``Type u``:
-->

换句话说，一个半群包括一个类型「载体（``carrier``）」和一个乘法 ``mul``，乘法满足结合性。
``instance`` 命令允许我们用 ``a * b`` 代替 ``Semigroup.mul S a b`` 只要我们有 ``a b : S.carrier``；
注意，Lean 可以根据 ``a`` 和 ``b`` 的类型推断出参数 ``S``。函数 ``Semigroup.carrier``
将类 ``Semigroup`` 映射到种类 ``Type u``：

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
#check Semigroup.carrier
```

<!--
If we declare this function to be a coercion, then whenever we have a semigroup ``S : Semigroup``, we can write ``a : S`` instead of ``a : S.carrier``:
-->

如果我们声明该函数是一个强制转换函数，那么无论何时我们都有半群 ``S : Semigroup``,
我们可以写 ``a : S`` 而非 ``a : S.carrier``：

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c
```

<!--
It is the coercion that makes it possible to write ``(a b c : S)``. Note that, we define an instance of ``CoeSort Semigroup (Type u)`` instead of ``Coe Semigroup (Type u)``.
-->

由于强制转换，我们可以写 ``(a b c : S)``。
注意，我们定义了一个 ``CoeSort Semigroup (Type u)`` 的实例，
而非 ``Coe Semigroup (Type u)``。

<!--
By the *class of function types*, we mean the collection of Pi types ``(z : B) → C``. The third kind of coercion has the form:
-->

 **函数类型的类** ，是指 Π 类型集合 ``(z : B) → C``。第三种强制转换形式为：

```
    c : (x1 : A1) → ... → (xn : An) → (y : F x1 ... xn) → (z : B) → C
```

<!--
where ``F`` is again a family of types and ``B`` and ``C`` can depend on ``x1, ..., xn, y``. This makes it possible to write ``t s`` whenever ``t`` is an element of ``F a1 ... an``. In other words, the coercion enables us to view elements of ``F a1 ... an`` as functions. Continuing the example above, we can define the notion of a morphism between semigroups ``S1`` and ``S2``. That is, a function from the carrier of ``S1`` to the carrier of ``S2`` (note the implicit coercion) that respects the multiplication. The projection ``morphism.mor`` takes a morphism to the underlying function:
-->

其中 ``F`` 仍然是一个类型族，而 ``B`` 和 ``C`` 可以取决于 ``x1, ..., xn, y``。
这使得可以写 ``t s``，只要 ``t`` 是 ``F a1 ... an`` 的元素。
换句话说，转换使我们可以将 ``F a1 ... an`` 的元素视为函数。
继续上面的示例，我们可以定义半群 ``S1`` 和 ``S2`` 之间的态射的概念。
即，从 ``S1`` 的载体到 ``S2`` 的载体（注意隐式转换）关于乘法的一个函数。
投影 ``morphism.mor`` 将一个态射转化为底层函数。

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
# instance : CoeSort Semigroup (Type u) where
#   coe s := s.carrier
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor
```

<!--
As a result, it is a prime candidate for the third type of coercion.
-->

因此，它成为第三种强制转换的主要候选。

```lean
# structure Semigroup where
#   carrier : Type u
#   mul : carrier → carrier → carrier
#   mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
# instance (S : Semigroup) : Mul S.carrier where
#   mul a b := S.mul a b
# instance : CoeSort Semigroup (Type u) where
#   coe s := s.carrier
# structure Morphism (S1 S2 : Semigroup) where
#   mor : S1 → S2
#   resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)
instance (S1 S2 : Semigroup) : CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
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

<!--
With the coercion in place, we can write ``f (a * a * a)`` instead of ``f.mor (a * a * a)``. When the ``Morphism``, ``f``, is used where a function is expected, Lean inserts the coercion. Similar to ``CoeSort``, we have yet another class ``CoeFun`` for this class of coercions. The field ``F`` is used to specify the function type we are coercing to. This type may depend on the type we are coercing from.
-->

有了强制类型转换，我们可以直接写 ``f (a * a * a)`` 而不必写 ``f.mor (a * a * a)``。
当 ``Morphism``（态射）``f`` 被用于原本期望函数的位置时，
Lean 会自动插入强制转换。类似于 ``CoeSort``，我们还有另一个类 ``CoeFun``
用于这一类的强制转换。域 ``F`` 用于指定我们强制类型转换的目标函数类型。
此类型可能依赖于我们强制转换的原类型。
