<!--
Dependent Type Theory
-->

依值类型论
=====================

<!--
Dependent type theory is a powerful and expressive language, allowing
you to express complex mathematical assertions, write complex hardware
and software specifications, and reason about both of these in a
natural and uniform way. Lean is based on a version of dependent type
theory known as the *Calculus of Constructions*, with a countable
hierarchy of non-cumulative universes and inductive types. By the end
of this chapter, you will understand much of what this means.
-->

依值类型论（Dependent type theory）是一种强大而富有表达力的语言，允许你表达复杂的数学断言，编写复杂的硬件和软件规范，并以自然和统一的方式对这两者进行推理。Lean是基于一个被称为构造演算（Calculus of Constructions）的依值类型论的版本，它拥有一个可数的非累积性宇宙（non-cumulative universe）的层次结构以及归纳类型（Inductive type）。在本章结束时，你将学会一大部分。

<!--
## Simple Type Theory
-->

## 简单类型论

<!--
"Type theory" gets its name from the fact that every expression has an
associated *type*. For example, in a given context, ``x + 0`` may
denote a natural number and ``f`` may denote a function on the natural
numbers. For those who like precise definitions, a Lean natural number
is an arbitrary-precision unsigned integer.
-->

“类型论”得名于其中每个表达式都有一个*类型*。举例：在一个给定的语境中，``x + 0``可能表示一个自然数，``f``可能表示一个定义在自然数上的函数。Lean中的自然数是任意精度的无符号整数。

<!--
Here are some examples of how you can declare objects in Lean and
check their types.
-->

这里的一些例子展示了如何声明对象以及检查其类型。

<!--
```lean
/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```
-->

```lean
/- 定义一些常数 -/

def m : Nat := 1       -- m 是自然数
def n : Nat := 0
def b1 : Bool := true  -- b1 是布尔型
def b2 : Bool := false

/- 检查类型 -/

#check m            -- 输出: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"

/- 求值（Evaluate） -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false
```

<!--
Any text between ``/-`` and ``-/`` constitutes a comment block that is
ignored by Lean. Similarly, two dashes `--` indicate that the rest of
the line contains a comment that is also ignored. Comment blocks can
be nested, making it possible to "comment out" chunks of code, just as
in many programming languages.
-->

位于``/-``和``-/``之间的文本组成了一个注释块，会被Lean的编译器忽略。类似地，两条横线`--`后面也是注释。注释块可以嵌套，这样就可以“注释掉”一整块代码，这和任何程序语言都是一样的。

<!--
The ``def`` keyword declares new constant symbols into the
working environment. In the example above, `def m : Nat := 1`
defines a new constant `m` of type `Nat` whose value is `1`.
The ``#check`` command asks Lean to report their
types; in Lean, auxiliary commands that query the system for
information typically begin with the hash (#) symbol.
The `#eval` command asks Lean to evaluate the given expression.
You should try
declaring some constants and type checking some expressions on your
own. Declaring new objects in this manner is a good way to experiment
with the system.
-->

``def``关键字声明工作环境中的新常量符号。在上面的例子中，`def m : Nat := 1`定义了一个`Nat`类型的新常量`m`，其值为`1`。``#check``命令要求Lean给出它的类型，用于向系统询问信息的辅助命令都以井号(#)开头。`#eval`命令让Lean计算给出的表达式。你应该试试自己声明一些常量和检查一些表达式的类型。

<!--
What makes simple type theory powerful is that you can build new types
out of others. For example, if ``a`` and ``b`` are types, ``a -> b``
denotes the type of functions from ``a`` to ``b``, and ``a × b``
denotes the type of pairs consisting of an element of ``a`` paired
with an element of ``b``, also known as the *Cartesian product*. Note
that `×` is a Unicode symbol. The judicious use of Unicode improves
legibility, and all modern editors have great support for it. In the
Lean standard library, you often see Greek letters to denote types,
and the Unicode symbol `→` as a more compact version of `->`.
-->

简单类型论的强大之处在于，你可以从其他类型中构建新的类型。例如，如果``a``和``b``是类型，``a -> b``表示从``a``到``b``的函数类型，``a × b``表示由``a``元素与``b``元素配对构成的类型，也称为*笛卡尔积*。注意`×`是一个Unicode符号，可以使用``\times``或简写``\tim``来输入。合理使用Unicode提高了易读性，所有现代编辑器都支持它。在Lean标准库中，你经常看到希腊字母表示类型，Unicode符号`→`是`->`的更紧凑版本。

<!--
```lean
#check Nat → Nat      -- type the arrow as "\to" or "\r"
#check Nat -> Nat     -- alternative ASCII notation

#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  same type as above

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```
-->

```lean
#check Nat → Nat      -- 用"\to" or "\r"来打出这个箭头
#check Nat -> Nat     -- 也可以用 ASCII 符号

#check Nat × Nat      -- 用"\times"打出乘号
#check Prod Nat Nat   -- 换成ASCII 符号

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  --  结果和上一个一样

#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- 一个“泛函”

#check Nat.succ     -- Nat → Nat
#check (0, 1)       -- Nat × Nat
#check Nat.add      -- Nat → Nat → Nat

#check Nat.succ 2   -- Nat
#check Nat.add 3    -- Nat → Nat
#check Nat.add 5 2  -- Nat
#check (5, 9).1     -- Nat
#check (5, 9).2     -- Nat

#eval Nat.succ 2   -- 3
#eval Nat.add 5 2  -- 7
#eval (5, 9).1     -- 5
#eval (5, 9).2     -- 9
```

<!--
Once again, you should try some examples on your own.

Let's take a look at some basic syntax. You can enter the unicode
arrow ``→`` by typing ``\to`` or ``\r`` or ``\->``. You can also use the
ASCII alternative ``->``, so the expressions ``Nat -> Nat`` and ``Nat →
Nat`` mean the same thing. Both expressions denote the type of
functions that take a natural number as input and return a natural
number as output. The unicode symbol ``×`` for the Cartesian product
is entered as ``\times``. You will generally use lower-case Greek
letters like ``α``, ``β``, and ``γ`` to range over types. You can
enter these particular ones with ``\a``, ``\b``, and ``\g``.

There are a few more things to notice here. First, the application of
a function ``f`` to a value ``x`` is denoted ``f x`` (e.g., `Nat.succ 2`).
Second, when writing type expressions, arrows associate to the *right*; for
example, the type of ``Nat.add`` is ``Nat → Nat → Nat`` which is equivalent
to `Nat → (Nat → Nat)`. Thus you can
view ``Nat.add`` as a function that takes a natural number and returns
another function that takes a natural number and returns a natural
number. In type theory, this is generally more convenient than
writing ``Nat.add`` as a function that takes a pair of natural numbers as
input and returns a natural number as output. For example, it allows
you to "partially apply" the function ``Nat.add``.  The example above shows
that ``Nat.add 3`` has type ``Nat → Nat``, that is, ``Nat.add 3`` returns a
function that "waits" for a second argument, ``n``, which is then
equivalent to writing ``Nat.add 3 n``.
-->

同样，你应该自己尝试一些例子。

让我们看一些基本语法。你可以通过输入``\to``或者``\r``或者``\->``来输入``→``。你也可以就用ASCII码``->``，所以表达式``Nat -> Nat``和``Nat → Nat``意思是一样的，都表示以一个自然数作为输入并返回一个自然数作为输出的函数类型。Unicode符号``×``是笛卡尔积，用``\times``输入。小写的希腊字母``α``，``β``，和``γ``等等常用来表示类型变量，可以用``\a``，``\b``，和``\g``来输入。

这里还有一些需要注意的事情。第一，函数``f``应用到值``x``上写为``f x``(例：`Nat.succ 2`)。第二，当写类型表达式时，箭头是*右结合*的；例如，``Nat.add``的类型是``Nat → Nat → Nat``，等价于``Nat → (Nat → Nat)``。

因此你可以把``Nat.add``看作一个函数，它接受一个自然数并返回另一个函数，该函数接受一个自然数并返回一个自然数。在类型论中，把``Nat.add``函数看作接受一对自然数作为输入并返回一个自然数作为输出的函数通常会更方便。系统允许你“部分应用”函数``Nat.add``，比如``Nat.add 3``具有类型``Nat → Nat``，即``Nat.add 3``返回一个“等待”第二个参数``n``的函数，然后可以继续写``Nat.add 3 n``。

<!-- Taking a function ``h`` of type ``Nat
× Nat → Nat`` and "redefining" it to look like ``g`` is a process
known as *currying*. -->

> 注：取一个类型为``Nat × Nat → Nat``的函数，然后“重定义”它，让它变成``Nat → Nat → Nat``类型，这个过程被称作*柯里化*（currying）。

<!--
You have seen that if you have ``m : Nat`` and ``n : Nat``, then
``(m, n)`` denotes the ordered pair of ``m`` and ``n`` which is of
type ``Nat × Nat``. This gives you a way of creating pairs of natural
numbers. Conversely, if you have ``p : Nat × Nat``, then you can write
``p.1 : Nat`` and ``p.2 : Nat``. This gives you a way of extracting
its two components.
-->

如果你有``m : Nat``和``n : Nat``，那么``(m, n)``表示``m``和``n``组成的有序对，其类型为``Nat × Nat``。这个方法可以制造自然数对。反过来，如果你有``p : Nat × Nat``，之后你可以写``p.1 : Nat``和``p.2 : Nat``。这个方法用于提取它的两个组件。

<!--
## Types as objects
-->

## 类型作为对象

<!--
One way in which Lean's dependent type theory extends simple type
theory is that types themselves --- entities like ``Nat`` and ``Bool``
--- are first-class citizens, which is to say that they themselves are
objects. For that to be the case, each of them also has to have a
type.
-->

Lean所依据的依值类型论对简单类型论的其中一项升级是，类型本身（如``Nat``和``Bool``这些东西）也是对象，因此也具有类型。

```lean
#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat
```

<!--
You can see that each one of the expressions above is an object of
type ``Type``. You can also declare new constants for types:
-->

上面的每个表达式都是类型为``Type``的对象。你也可以为类型声明新的常量:

```lean
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type
```

<!--
As the example above suggests, you have already seen an example of a function of type
``Type → Type → Type``, namely, the Cartesian product `Prod`:
-->

正如上面所示，你已经看到了一个类型为``Type → Type → Type``的函数例子，即笛卡尔积 `Prod`：

```lean
def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type
```

<!--
Here is another example: given any type ``α``, the type ``List α``
denotes the type of lists of elements of type ``α``.
-->

这里有另一个例子：给出任意类型``α``，那么类型``List α``是类型为``α``的元素的列表的类型。

```lean
def α : Type := Nat

#check List α    -- Type
#check List Nat  -- Type
```

<!--
Given that every expression in Lean has a type, it is natural to ask:
what type does ``Type`` itself have?
-->

看起来Lean中任何表达式都有一个类型，因此你可能会想到：``Type``自己的类型是什么？

```lean
#check Type      -- Type 1
```

<!--
You have actually come up against one of the most subtle aspects of
Lean's typing system. Lean's underlying foundation has an infinite
hierarchy of types:
-->

实际上，这是Lean系统的一个最微妙的方面：Lean的底层基础有无限的类型层次：

```lean
#check Type     -- Type 1
#check Type 1   -- Type 2
#check Type 2   -- Type 3
#check Type 3   -- Type 4
#check Type 4   -- Type 5
```

<!--
Think of ``Type 0`` as a universe of "small" or "ordinary" types.
``Type 1`` is then a larger universe of types, which contains ``Type
0`` as an element, and ``Type 2`` is an even larger universe of types,
which contains ``Type 1`` as an element. The list is indefinite, so
that there is a ``Type n`` for every natural number ``n``. ``Type`` is
an abbreviation for ``Type 0``:
-->

可以将``Type 0``看作是一个由“小”或“普通”类型组成的宇宙。然后，``Type 1``是一个更大的类型范围，其中包含``Type 0``作为一个元素，而``Type 2``是一个更大的类型范围，其中包含``Type 1``作为一个元素。这个列表是不确定的，所以对于每个自然数``n``都有一个``Type n``。``Type``是``Type 0``的缩写：

```lean
#check Type
#check Type 0
```

<!--
The following table may help concretize the relationships being discussed.
Movement along the x-axis represents a change in the universe, while movement
along the y-axis represents a change in what is sometimes referred to as
"degree".
-->

下表可能有助于具体说明所讨论的关系。行方向代表宇宙的变化，列方向代表有时被称为“度”的变化。

|        |               |               |                 |                        |     |
|:------:|:-------------:|:-------------:|:---------------:|:----------------------:|:---:|
| sort   | Prop (Sort 0) | Type (Sort 1) | Type 1 (Sort 2) | Type 2 (Sort 3)        | ... |
| type   | True          | Bool          |   Nat -> Type   | Type -> Type 1         | ... |
| term   | trivial       | true          | fun n => Fin n  | fun (_ : Type) => Type | ... |


<!--
Some operations, however, need to be *polymorphic* over type
universes. For example, ``List α`` should make sense for any type
``α``, no matter which type universe ``α`` lives in. This explains the
type signature of the function ``List``:
-->

然而，有些操作需要在类型宇宙上具有**多态**（polymorphic）。例如，``List α``应该对任何类型的``α``都有意义，无论``α``存在于哪种类型的宇宙中。所以函数``List``有如下的类型：

```lean
#check List    -- List.{u} (α : Type u) : Type u
```

<!--
Here ``u`` is a variable ranging over type levels. The output of the
``#check`` command means that whenever ``α`` has type ``Type n``,
``List α`` also has type ``Type n``. The function ``Prod`` is
similarly polymorphic:
-->

这里``u``是一个遍取类型级别的变量。``#check``命令的输出意味着当``α``有类型``Type n``时，``List α``也有类型``Type n``。函数``Prod``具有类似的多态性：

```lean
#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)
```

<!--
To define polymorphic constants, Lean allows you to
declare universe variables explicitly using the `universe` command:
-->

你可以使用 `universe` 命令来声明宇宙变量，这样就可以定义多态常量：

```lean
universe u

def F (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```

<!--
You can avoid the universe command by providing the universe parameters when defining F.
-->

可以通过在定义F时提供universe参数来避免使用`universe`命令：

```lean
def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u
```


<!--
## Function Abstraction and Evaluation
-->

## 函数抽象和求值

Lean提供 `fun` (或 `λ`)关键字用于从给定表达式创建函数，如下所示：

<!--
```lean
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ and fun mean the same thing
#check fun x => x + 5     -- Nat inferred
#check λ x => x + 5       -- Nat inferred
```
-->

```lean
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- λ 和 fun 是同义词
#check fun x : Nat => x + 5     -- 同上
#check λ x : Nat => x + 5       -- 同上
```

<!--
You can evaluate a lambda function by passing the required parameters:
-->

你可以通过传递所需的参数来计算lambda函数：

```lean
#eval (λ x : Nat => x + 5) 10    -- 15
```

<!--
Creating a function from another expression is a process known as
*lambda abstraction*. Suppose you have the variable ``x : α`` and you can
construct an expression ``t : β``, then the expression ``fun (x : α)
=> t``, or, equivalently, ``λ (x : α) => t``, is an object of type ``α
→ β``. Think of this as the function from ``α`` to ``β`` which maps
any value ``x`` to the value ``t``.

Here are some more examples
-->

从另一个表达式创建函数的过程称为**lambda 抽象**。假设你有一个变量``x : α``和一个表达式``t : β``，那么表达式``fun (x : α) => t``或者``λ (x : α) => t``是一个类型为``α → β``的对象。这个从``α``到``β``的函数把任意``x``映射到``t``。

这有些例子：

```lean
#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat
```

<!--
Lean interprets the final three examples as the same expression; in
the last expression, Lean infers the type of ``x`` and ``y`` from the
expression `if not y then x + 1 else x + 2`.

Some mathematically common examples of operations of functions can be
described in terms of lambda abstraction:
-->

Lean将这三个例子解释为相同的表达式；在最后一个表达式中，Lean可以从表达式`if not y then x + 1 else x + 2`推断``x``和``y``的类型。

一些数学上常见的函数运算的例子可以用lambda抽象的项来描述:

```lean
def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool
```

<!--
Think about what these expressions mean. The expression
``fun x : Nat => x`` denotes the identity function on ``Nat``, the
expression ``fun x : Nat => true`` denotes the constant function that
always returns ``true``, and ``fun x : Nat => g (f x)`` denotes the
composition of ``f`` and ``g``.  You can, in general, leave off the
type annotation and let Lean infer it for you.  So, for example, you
can write ``fun x => g (f x)`` instead of ``fun x : Nat => g (f x)``.

You can pass functions as parameters and by giving them names `f`
and `g` you can then use those functions in the implementation:
-->

看看这些表达式的意思。表达式``fun x : Nat => x``代表``Nat``上的恒等函数，表达式``fun x : Nat => true``表示一个永远输出``true``的常值函数，表达式``fun x : Nat => g (f x)``表示``f``和``g``的复合。一般来说，你可以省略类型注释，让Lean自己推断它。因此你可以写``fun x => g (f x)``来代替``fun x : Nat => g (f x)``。

你可以以函数作为参数，通过给它们命名`f`和`g`，你可以在实现中使用这些函数：

```lean
#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool
```

<!--
You can also pass types as parameters:
-->

你还可以以类型作为参数：

```lean
#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
```
<!--
The last expression, for example, denotes the function that takes
three types, ``α``, ``β``, and ``γ``, and two functions, ``g : β → γ``
and ``f : α → β``, and returns the composition of ``g`` and ``f``.
(Making sense of the type of this function requires an understanding
of dependent products, which will be explained below.)

The general form of a lambda expression is ``fun x : α => t``, where
the variable ``x`` is a "bound variable": it is really a placeholder,
whose "scope" does not extend beyond the expression ``t``.  For
example, the variable ``b`` in the expression ``fun (b : β) (x : α) => b``
has nothing to do with the constant ``b`` declared earlier.  In fact,
the expression denotes the same function as ``fun (u : β) (z : α) => u``.

Formally, expressions that are the same up to a renaming of bound
variables are called *alpha equivalent*, and are considered "the
same." Lean recognizes this equivalence.

Notice that applying a term ``t : α → β`` to a term ``s : α`` yields
an expression ``t s : β``. Returning to the previous example and
renaming bound variables for clarity, notice the types of the
following expressions:
-->

这个表达式表示一个接受三个类型``α``，``β``和``γ``和两个函数``g : β → γ``和``f : α → β``，并返回的``g``和``f``的复合的函数。(理解这个函数的类型需要理解依值积类型，下面将对此进行解释。)

lambda表达式的一般形式是``fun x : α => t``，其中变量``x``是一个**绑定变量**（bound variable）：它实际上是一个占位符，其“作用域”没有扩展到表达式``t``之外。例如，表达式``fun (b : β) (x : α) => b``中的变量``b``与前面声明的常量``b``没有任何关系。事实上，这个表达式表示的函数与``fun (u : β) (z : α) => u``是一样的。形式上，可以通过给绑定变量重命名来使形式相同的表达式被看作是**alpha等价**的，也就是被认为是“一样的”。Lean认识这种等价性。

注意到项``t : α → β``应用到项``s : α``上导出了表达式``t s : β``。回到前面的例子，为清晰起见给绑定变量重命名，注意以下表达式的类型:

```lean
#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
  -- Bool
```

<!--
As expected, the expression ``(fun x : Nat =>  x) 1`` has type ``Nat``.
In fact, more should be true: applying the expression ``(fun x : Nat
=> x)`` to ``1`` should "return" the value ``1``. And, indeed, it does:
-->

表达式``(fun x : Nat =>  x) 1``的类型是``Nat``。实际上，应用``(fun x : Nat => x)``到``1``上返回的值是``1``。

```lean
#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
```

<!--
You will see later how these terms are evaluated. For now, notice that
this is an important feature of dependent type theory: every term has
a computational behavior, and supports a notion of *normalization*. In
principle, two terms that reduce to the same value are called
*definitionally equal*. They are considered "the same" by Lean's type
checker, and Lean does its best to recognize and support these
identifications.

Lean is a complete programming language. It has a compiler that
generates a binary executable and an interactive interpreter. You can
use the command `#eval` to execute expressions, and it is the
preferred way of testing your functions.
-->

稍后你将看到这些项是如何计算的。现在，请注意这是依值类型论的一个重要特征：每个项都有一个计算行为，并支持“标准化”的概念。从原则上讲，两个可以化约为相同形式的项被称为“定义等价”。它们被Lean的类型检查器认为是“相同的”，并且Lean尽其所能地识别和支持这些识别结果。

Lean是个完备的编程语言。它有一个生成二进制可执行文件的编译器，和一个交互式解释器。你可以用`#eval`命令执行表达式，这也是测试你的函数的好办法。

<!--
Note that `#eval` and
`#reduce` are *not* equivalent. The command `#eval` first compiles
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

> 注意到`#eval`和`#reduce`*不是*等价的。`#eval`命令首先把Lean表达式编译成中间表示（intermediate representation, IR）然后用一个解释器来执行这个IR。某些内建类型（例如，`Nat`、`String`、`Array`）在IR中有更有效率的表示。IR支持使用对Lean不透明的外部函数。
> ``#reduce``命令建立在一个规约引擎上，类似于在Lean的可信内核中使用的那个，它是负责检查和验证表达式和证明正确性的那一部分。它的效率不如``#eval``，且将所有外部函数视为不透明的常量。之后你将了解到这两个命令之间还有其他一些差异。

<!--
## Definitions
-->

## 定义

<!--
Recall that the ``def`` keyword provides one important way of declaring new named
objects.
-->

``def``关键字提供了一个声明新对象的重要方式。

```lean
def double (x : Nat) : Nat :=
  x + x
```

<!--
This might look more familiar to you if you know how functions work in
other programming languages. The name `double` is defined as a
function that takes an input parameter `x` of type `Nat`, where the
result of the call is `x + x`, so it is returning type `Nat`. You
can then invoke this function using:
-->

这很类似其他编程语言中的函数。名字`double`被定义为一个函数，它接受一个类型为`Nat`的输入参数`x`，其结果是`x + x`，因此它返回类型`Nat`。然后你可以调用这个函数:

```lean
# def double (x : Nat) : Nat :=
#  x + x
#eval double 3    -- 6
```

<!--
In this case you can think of `def` as a kind of named `lambda`.
The following yields the same result:
-->

在这种情况下你可以把`def`想成一种`lambda`。下面给出了相同的结果：

```lean
def double : Nat → Nat :=
  fun x => x + x

#eval double 3    -- 6
```

<!--
You can omit the type declarations when Lean has enough information to
infer it.  Type inference is an important part of Lean:
-->

当Lean有足够的信息来推断时，你可以省略类型声明。类型推断是Lean的重要组成部分:

```lean
def double :=
  fun (x : Nat) => x + x
```

<!--
The general form of a definition is ``def foo : α := bar`` where
``α`` is the type returned from the expression ``bar``.  Lean can
usually infer the type ``α``, but it is often a good idea to write it
explicitly.  This clarifies your intention, and Lean will flag an
error if the right-hand side of the definition does not have a matching
type.

The right hand side `bar` can be any expression, not just a lambda.
So `def` can also be used to simply name a value like this:
-->

定义的一般形式是``def foo : α := bar``，其中``α``是表达式``bar``返回的类型。Lean通常可以推断类型``α``，但是精确写出它可以澄清你的意图，并且如果定义的右侧没有匹配你的类型，Lean将标记一个错误。

`bar`可以是任何一个表达式，不只是一个lambda表达式。因此`def`也可以用于给一些值命名，例如：


```lean
def pi := 3.141592654
```

<!--
`def` can take multiple input parameters.  Let's create one
that adds two natural numbers:
-->

`def`可以接受多个输入参数。比如定义两自然数之和：

```lean
def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5
```

<!--
The parameter list can be separated like this:
-->

参数列表可以像这样分开写：

```lean
# def double (x : Nat) : Nat :=
#  x + x
def add (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22
```

<!--
Notice here we called the `double` function to create the first
parameter to `add`.

You can use other more interesting expressions inside a `def`:
-->

注意到这里我们使用了`double`函数来创建`add`函数的第一个参数。

你还可以在`def`中写一些更有趣的表达式：

```lean
def greater (x y : Nat) :=
  if x > y then x
  else y
```

<!--
You can probably guess what this one will do.

You can also define a function that takes another function as input.
The following calls a given function twice passing the output of the
first invocation to the second:
-->

猜猜这个可以做什么。

还可以定义一个函数，该函数接受另一个函数作为输入。下面调用一个给定函数两次，将第一次调用的输出传递给第二次:

```lean
# def double (x : Nat) : Nat :=
#  x + x
def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2   -- 8
```

<!--
Now to get a bit more abstract, you can also specify arguments that
are like type parameters:
-->

现在为了更抽象一点，你也可以指定类型参数等：

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

<!--
This means `compose` is a function that takes any two functions as input
arguments, so long as those functions each take only one input.
The type algebra `β → γ` and `α → β` means it is a requirement
that the type of the output of the second function must match the
type of the input to the first function - which makes sense, otherwise
the two functions would not be composable.

`compose` also takes a 3rd argument of type `α` which
it uses to invoke the second function (locally named `f`) and it
passes the result of that function (which is type `β`) as input to the
first function (locally named `g`).  The first function returns a type
`γ` so that is also the return type of the `compose` function.

`compose` is also very general in that it works over any type
`α β γ`.  This means `compose` can compose just about any 2 functions
so long as they each take one parameter, and so long as the type of
output of the second matches the input of the first.  For example:
-->

这句代码的意思是：函数`compose`首先接受任何两个函数作为参数，这其中两个函数各自接受一个输入。类型`β → γ`和`α → β`意思是要求第二个函数的输出类型必须与第一个函数的输入类型匹配，否则这两个函数将无法复合。

`compose`再接受一个类型为`α`的参数作为第二个函数（这里叫做`f`）的输入，通过这个函数之后的返回结果类型为`β`，再作为第一个函数（这里叫做`g`）的输入。第一个函数返回类型为`γ`，这就是`compose`函数最终返回的类型。

`compose`可以在任意的类型`α β γ`上使用，它可以复合任意两个函数，只要前一个的输出类型是后一个的输入类型。举例：

```lean
# def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
#  g (f x)
# def double (x : Nat) : Nat :=
#  x + x
def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3  -- 18
```

<!--
Local Definitions
-----------------
-->

## 局部定义

<!--
Lean also allows you to introduce "local" definitions using the
``let`` keyword. The expression ``let a := t1; t2`` is
definitionally equal to the result of replacing every occurrence of
``a`` in ``t2`` by ``t1``.
-->

Lean还允许你使用``let``关键字来引入“局部定义”。表达式``let a := t1; t2``定义等价于把``t2``中所有的``a``替换成``t1``的结果。

```lean
#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2   -- 16
```

<!--
Here, ``twice_double x`` is definitionally equal to the term ``(x + x) * (x + x)``.

You can combine multiple assignments by chaining ``let`` statements:
-->

这里``twice_double x``定义等价于``(x + x) * (x + x)``。

你可以连续使用多个``let``命令来进行多次替换：

```lean
#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64
```

<!--
The ``;`` can be omitted when a line break is used.
-->

换行可以省略分号``;``。

```lean
def t (x : Nat) : Nat :=
  let y := x + x
  y * y
```

<!--
Notice that the meaning of the expression ``let a := t1; t2`` is very
similar to the meaning of ``(fun a => t2) t1``, but the two are not
the same. In the first expression, you should think of every instance
of ``a`` in ``t2`` as a syntactic abbreviation for ``t1``. In the
second expression, ``a`` is a variable, and the expression
``fun a => t2`` has to make sense independently of the value of ``a``.
The ``let`` construct is a stronger means of abbreviation, and there
are expressions of the form ``let a := t1; t2`` that cannot be
expressed as ``(fun a => t2) t1``. As an exercise, try to understand
why the definition of ``foo`` below type checks, but the definition of
``bar`` does not.
-->

表达式``let a := t1; t2``的意思很类似``(fun a => t2) t1``，但是这两者并不一样。前者中你要把``t2``中每一个``a``的实例考虑成``t1``的一个缩写。后者中``a``是一个变量，表达式``fun a => t2``不依赖于``a``的取值而可以单独具有意义。作为一个对照，考虑为什么下面的``foo``定义是合法的，但``bar``不行（因为在确定了``x``所属的``a``是什么之前，是无法让它``+ 2``的）。

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```

<!--
# Variables and Sections
-->

## 变量和小节

<!--
Consider the following three function definitions:
-->

考虑下面这三个函数定义：

```lean
def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))
```

<!--
Lean provides you with the ``variable`` command to make such
declarations look more compact:
-->

Lean提供``variable``指令来让这些声明变得紧凑：

```lean
variable (α β γ : Type)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (h : α → α) (x : α) : α :=
  h (h (h x))
```

<!--
You can declare variables of any type, not just ``Type`` itself:
-->

你可以声明任意类型的变量，不只是``Type``类型：

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

<!--
Printing them out shows that all three groups of definitions have
exactly the same effect.

The ``variable`` command instructs Lean to insert the declared
variables as bound variables in definitions that refer to them by
name. Lean is smart enough to figure out which variables are used
explicitly or implicitly in a definition. You can therefore proceed as
though ``α``, ``β``, ``γ``, ``g``, ``f``, ``h``, and ``x`` are fixed
objects when you write your definitions, and let Lean abstract the
definitions for you automatically.

When declared in this way, a variable stays in scope until the end of
the file you are working on. Sometimes, however, it is useful to limit
the scope of a variable. For that purpose, Lean provides the notion of
a ``section``:
-->

输出结果表明所有三组定义具有完全相同的效果。

``variable``命令指示Lean将声明的变量作为绑定变量插入定义中，这些定义通过名称引用它们。Lean足够聪明，它能找出定义中显式或隐式使用哪些变量。因此在写定义时，你可以将``α``、``β``、``γ``、``g``、``f``、``h``和``x``视为固定的对象，并让Lean自动抽象这些定义。

当以这种方式声明时，变量将一直保持存在，直到所处理的文件结束。然而，有时需要限制变量的作用范围。Lean提供了小节标记``section``来实现这个目的：

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

<!--
When the section is closed, the variables go out of scope, and cannot
be referenced any more.

You do not have to indent the lines within a section. Nor do you have
to name a section, which is to say, you can use an anonymous
``section`` / ``end`` pair. If you do name a section, however, you
have to close it using the same name. Sections can also be nested,
which allows you to declare new variables incrementally.
-->

当一个小节结束后，变量不再发挥作用。

你不需要缩进一个小节中的行。你也不需要命名一个小节，也就是说，你可以使用一个匿名的``section`` /``end``对。但是，如果你确实命名了一个小节，你必须使用相同的名字关闭它。小节也可以嵌套，这允许你逐步增加声明新变量。

<!--
# Namespaces
-->

## 命名空间

<!--
Lean provides you with the ability to group definitions into nested,
hierarchical *namespaces*:
-->

Lean可以让你把定义放进一个“命名空间”（``namespace``）里，并且命名空间也是层次化的：

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

<!--
When you declare that you are working in the namespace ``Foo``, every
identifier you declare has a full name with prefix "``Foo.``". Within
the namespace, you can refer to identifiers by their shorter names,
but once you end the namespace, you have to use the longer names.
Unlike `section`, namespaces require a name. There is only one
anonymous namespace at the root level.

The ``open`` command brings the shorter names into the current
context. Often, when you import a module, you will want to open one or
more of the namespaces it contains, to have access to the short
identifiers. But sometimes you will want to leave this information
protected by a fully qualified name, for example, when they conflict
with identifiers in another namespace you want to use. Thus namespaces
give you a way to manage names in your working environment.

For example, Lean groups definitions and theorems involving lists into
a namespace ``List``.
-->

当你声明你在命名空间``Foo``中工作时，你声明的每个标识符都有一个前缀``Foo.``。在打开的命名空间中，可以通过较短的名称引用标识符，但是关闭命名空间后，必须使用较长的名称。与`section`不同，命名空间需要一个名称。只有一个匿名命名空间在根级别上。

``open``命令使你可以在当前使用较短的名称。通常，当你导入一个模块时，你会想打开它包含的一个或多个命名空间，以访问短标识符。但是，有时你希望将这些信息保留在一个完全限定的名称中，例如，当它们与你想要使用的另一个命名空间中的标识符冲突时。因此，命名空间为你提供了一种在工作环境中管理名称的方法。

例如，Lean把和列表相关的定义和定理都放在了命名空间``List``之中。

```lean
#check List.nil
#check List.cons
#check List.map
```
<!--
The command ``open List`` allows you to use the shorter names:
-->

``open List``命令允许你使用短一点的名字：
```lean
open List

#check nil
#check cons
#check map
```
<!--
Like sections, namespaces can be nested:
-->

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
<!--
Namespaces that have been closed can later be reopened, even in another file:
-->

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

<!--
Like sections, nested namespaces have to be closed in the order they
are opened. Namespaces and sections serve different purposes:
namespaces organize data and sections declare variables for insertion
in definitions. Sections are also useful for delimiting the scope of
commands such as ``set_option`` and ``open``.

In many respects, however, a ``namespace ... end`` block behaves the
same as a ``section ... end`` block. In particular, if you use the
``variable`` command within a namespace, its scope is limited to the
namespace. Similarly, if you use an ``open`` command within a
namespace, its effects disappear when the namespace is closed.
-->

与小节一样，嵌套的名称空间必须按照打开的顺序关闭。命名空间和小节有不同的用途：命名空间组织数据，小节声明变量，以便在定义中插入。小节对于分隔``set_option``和``open``等命令的范围也很有用。

然而，在许多方面，``namespace ... end``结构块和``section ... end``表现出来的特征是一样的。尤其是你在命名空间中使用``variable``命令时，它的作用范围被限制在命名空间里。类似地，如果你在命名空间中使用``open``命令，它的效果在命名空间关闭后消失。

<!--
## What makes dependent type theory dependent?
-->

## 依值类型论“依赖”着什么?

<!--
The short explanation is that types can depend on parameters. You
have already seen a nice example of this: the type ``List α`` depends
on the argument ``α``, and this dependence is what distinguishes
``List Nat`` and ``List Bool``. For another example, consider the
type ``Vector α n``, the type of vectors of elements of ``α`` of
length ``n``.  This type depends on *two* parameters: the type of the
elements in the vector (``α : Type``) and the length of the vector
``n : Nat``.

Suppose you wish to write a function ``cons`` which inserts a new
element at the head of a list. What type should ``cons`` have? Such a
function is *polymorphic*: you expect the ``cons`` function for
``Nat``, ``Bool``, or an arbitrary type ``α`` to behave the same way.
So it makes sense to take the type to be the first argument to
``cons``, so that for any type, ``α``, ``cons α`` is the insertion
function for lists of type ``α``. In other words, for every ``α``,
``cons α`` is the function that takes an element ``a : α`` and a list
``as : List α``, and returns a new list, so you have ``cons α a as : List α``.

It is clear that ``cons α`` should have type ``α → List α → List α``.
But what type should ``cons`` have?  A first guess might be
``Type → α → List α → List α``, but, on reflection, this does not make
sense: the ``α`` in this expression does not refer to anything,
whereas it should refer to the argument of type ``Type``.  In other
words, *assuming* ``α : Type`` is the first argument to the function,
the type of the next two elements are ``α`` and ``List α``. These
types vary depending on the first argument, ``α``.
-->

简单地说，类型可以依赖于参数。你已经看到了一个很好的例子：类型``List α``依赖于参数``α``，而这种依赖性是区分``List Nat``和``List Bool``的关键。另一个例子，考虑类型``Vector α n``，即长度为``n``的``α``元素的向量类型。这个类型取决于*两个*参数：向量中元素的类型``α : Type``和向量的长度``n : Nat``。

假设你希望编写一个函数``cons``，它在列表的开头插入一个新元素。``cons``应该有什么类型？这样的函数是*多态的*（polymorphic）：你期望``Nat``，``Bool``或任意类型``α``的``cons``函数表现相同的方式。因此，将类型作为``cons``的第一个参数是有意义的，因此对于任何类型``α``，``cons α``是类型``α``列表的插入函数。换句话说，对于每个``α``，``cons α``是将元素``a : α``插入列表``as : List α``的函数，并返回一个新的列表，因此有``cons α a as : List α``。

很明显，``cons α``具有类型``α → List α → List α``，但是``cons``具有什么类型？如果我们假设是``Type → α → list α → list α``，那么问题在于，这个类型表达式没有意义：``α``没有任何的所指，但它实际上指的是某个类型``Type``。换句话说，*假设*``α : Type``是函数的首个参数，之后的两个参数的类型是``α``和``List α``，它们依赖于首个参数``α``。

```lean
def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α
```

<!--
This is an instance of a *dependent function type*, or *dependent
arrow type*. Given ``α : Type`` and ``β : α → Type``, think of ``β``
as a family of types over ``α``, that is, a type ``β a`` for each
``a : α``. In that case, the type ``(a : α) → β a`` denotes the type
of functions ``f`` with the property that, for each ``a : α``, ``f a``
is an element of ``β a``. In other words, the type of the value
returned by ``f`` depends on its input.

Notice that ``(a : α) → β`` makes sense for any expression ``β :
Type``. When the value of ``β`` depends on ``a`` (as does, for
example, the expression ``β a`` in the previous paragraph),
``(a : α) → β`` denotes a dependent function type. When ``β`` doesn't
depend on ``a``, ``(a : α) → β`` is no different from the type
``α → β``.  Indeed, in dependent type theory (and in Lean), ``α → β``
is just notation for ``(a : α) → β`` when ``β`` does not depend on ``a``.

Returning to the example of lists, you can use the command `#check` to
inspect the type of the following `List` functions.  The ``@`` symbol
and the difference between the round and curly braces will be
explained momentarily.
-->

这就是*依值函数类型*，或者*依值箭头类型*的一个例子。给定``α : Type``和``β : α → Type``，把``β``考虑成``α``之上的类型族，也就是说，对于每个``a : α``都有类型``β a``。在这种情况下，类型``(a : α) → β a``表示的是具有如下性质的函数``f``的类型：对于每个``a : α``，``f a``是``β a``的一个元素。换句话说，``f``返回值的类型取决于其输入。

注意到``(a : α) → β``对于任意表达式``β : Type``都有意义。当``β``的值依赖于``a``（例如，在前一段的表达式``β a``），``(a : α) → β``表示一个依值函数类型。当``β``的值不依赖于``a``，``(a : α) → β``与类型``α → β``无异。实际上，在依值类型论（以及Lean）中，``α → β``表达的意思就是当``β``的值不依赖于``a``时的``(a : α) → β``。【注】

> 译者注：在依值类型论的数学符号体系中，依值类型是用``Π``符号来表达的，在Lean 3中还使用这种表达，例如``Π x : α, β x``。Lean 4抛弃了这种不友好的写法。``(x : α) → β x``这种写法在引入“构造器”之后意义会更明朗一些（见下一个注释），对于来自数学背景的读者可以把它类比于``forall x : α, β x``这种写法（这也是合法的Lean语句），关于前一种符号在[量词与等价](./quantifiers_and_equality.md)一章中有更详细的说明。同时，依值类型有着更丰富的引入动机，推荐读者寻找一些拓展读物。

回到列表的例子，你可以使用`#check`命令来检查下列的`List`函数。``@``符号以及圆括号和花括号之间的区别将在后面解释。

```lean
#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α
```

<!--
Just as dependent function types ``(a : α) → β a`` generalize the
notion of a function type ``α → β`` by allowing ``β`` to depend on
``α``, dependent Cartesian product types ``(a : α) × β a`` generalize
the Cartesian product ``α × β`` in the same way. Dependent products
are also called *sigma* types, and you can also write them as
`Σ a : α, β a`. You can use `⟨a, b⟩` or `Sigma.mk a b` to create a
dependent pair.  The `⟨` and `⟩` characters may be typed with
`\langle` and `\rangle` or `\<` and `\>`, respectively.
-->

就像依值函数类型``(a : α) → β a``通过允许``β``依赖``α``从而推广了函数类型``α → β``，依值笛卡尔积类型``(a : α) × β a``同样推广了笛卡尔积``α × β``。依值积类型又称为*sigma*类型，可写成`Σ a : α, β a`。你可以用`⟨a, b⟩`或者`Sigma.mk a b`来创建依值对。 `⟨`和`⟩`符号可以用`\langle`和`\rangle`或者`\<`和`\>`来输入.

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

<!--
The functions `f` and `g` above denote the same function.
-->

函数`f`和`g`表达的是同样的函数。


<!--
Implicit Arguments
------------------
-->

## 隐参数

<!--
Suppose we have an implementation of lists as:
-->

假设我们有一个列表的实现如下：

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α
```

<!--
Then, you can construct lists of `Nat` as follows.
-->

然后，你可以建立一个自然数列表如下：

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
# #check Lst          -- Type u_1 → Type u_1
# #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
# #check Lst.nil      -- (α : Type u_1) → Lst α
# #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
#check Lst.cons Nat 0 (Lst.nil Nat)

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs
```

<!--
Because the constructors are polymorphic over types, we have to insert
the type ``Nat`` as an argument repeatedly. But this information is
redundant: one can infer the argument ``α`` in
``Lst.cons Nat 5 (Lst.nil Nat)`` from the fact that the second argument, ``5``, has
type ``Nat``. One can similarly infer the argument in ``Lst.nil Nat``, not
from anything else in that expression, but from the fact that it is
sent as an argument to the function ``Lst.cons``, which expects an element
of type ``Lst α`` in that position.

This is a central feature of dependent type theory: terms carry a lot
of information, and often some of that information can be inferred
from the context. In Lean, one uses an underscore, ``_``, to specify
that the system should fill in the information automatically. This is
known as an "implicit argument."
-->

由于构造器对类型是多态的【注】，我们需要重复插入类型``Nat``作为一个参数。但是这个信息是多余的：我们可以推断表达式``Lst.cons Nat 5 (Lst.nil Nat)``中参数``α``的类型，这是通过第二个参数``5``的类型是``Nat``来实现的。类似地，我们可以推断``Lst.nil Nat``中参数的类型，这是通过它作为函数``Lst.cons``的一个参数，且这个函数在这个位置需要接收的是一个具有``Lst α``类型的参数来实现的。

> 译者注：“构造器”（Constructor）的概念前文未加解释，对类型论不熟悉的读者可能会困惑。它指的是一种“依值类型的类型”，也可以看作“类型的构造器”，例如``λ α : α -> α``甚至可看成``⋆ -> ⋆``。当给``α``或者``⋆``赋予一个具体的类型时，这个表达式就成为了一个类型。前文中``(x : α) → β x``中的``β``就可以看成一个构造器，``(x : α)``就是传进的类型参数。原句“构造器对类型是多态的”意为给构造器中放入不同类型时它会变成不同类型。

这是依值类型论的一个主要特征：项包含大量信息，而且通常可以从上下文推断出一些信息。在Lean中，我们使用下划线``_``来指定系统应该自动填写信息。这就是所谓的“隐参数”。

```lean
# universe u
# def Lst (α : Type u) : Type u := List α
# def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
# def Lst.nil (α : Type u) : Lst α := List.nil
# def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
# #check Lst          -- Type u_1 → Type u_1
# #check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
# #check Lst.nil      -- (α : Type u_1) → Lst α
# #check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
#check Lst.cons _ 0 (Lst.nil _)

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs
```

<!--
It is still tedious, however, to type all these underscores. When a
function takes an argument that can generally be inferred from
context, Lean allows you to specify that this argument should, by
default, be left implicit. This is done by putting the arguments in
curly braces, as follows:
-->

然而，敲这么多下划线仍然很无聊。当一个函数接受一个通常可以从上下文推断出来的参数时，Lean允许你指定该参数在默认情况下应该保持隐式。这是通过将参数放入花括号来实现的，如下所示:

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

<!--
All that has changed are the braces around ``α : Type u`` in the
declaration of the variables. We can also use this device in function
definitions:
-->

唯一改变的是变量声明中``α : Type u``周围的花括号。我们也可以在函数定义中使用这个技巧：

```lean
universe u
def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α
```

<!--
This makes the first argument to ``ident`` implicit. Notationally,
this hides the specification of the type, making it look as though
``ident`` simply takes an argument of any type. In fact, the function
``id`` is defined in the standard library in exactly this way. We have
chosen a nontraditional name here only to avoid a clash of names.

Variables can also be specified as implicit when they are declared with
the ``variable`` command:
-->

这使得``ident``的第一个参数是隐式的。从符号上讲，这隐藏了类型的说明，使它看起来好像``ident``只是接受任何类型的参数。事实上，函数``id``在标准库中就是以这种方式定义的。我们在这里选择一个非传统的名字只是为了避免名字的冲突。

``variable``命令也可以用这种技巧来来把变量变成隐式的：

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

<!--
This definition of ``ident`` here has the same effect as the one
above.

Lean has very complex mechanisms for instantiating implicit arguments,
and we will see that they can be used to infer function types,
predicates, and even proofs. The process of instantiating these
"holes," or "placeholders," in a term is often known as
*elaboration*. The presence of implicit arguments means that at times
there may be insufficient information to fix the meaning of an
expression precisely. An expression like ``id`` or ``List.nil`` is
said to be *polymorphic*, because it can take on different meanings in
different contexts.

One can always specify the type ``T`` of an expression ``e`` by
writing ``(e : T)``. This instructs Lean's elaborator to use the value
``T`` as the type of ``e`` when trying to resolve implicit
arguments. In the second pair of examples below, this mechanism is
used to specify the desired types of the expressions ``id`` and
``List.nil``:
-->

此处定义的``ident``和上面那个效果是一样的。

Lean有非常复杂的机制来实例化隐参数，我们将看到它们可以用来推断函数类型、谓词，甚至证明。实例化这些“洞”或“占位符”的过程通常被称为**繁饰**（Elaboration）。隐参数的存在意味着有时可能没有足够的信息来精确地确定表达式的含义。像``id``或``List.nil``这样的表达式被认为是“多态的”，因为它可以在不同的上下文中具有不同的含义。

可以通过写``(e : T)``来指定表达式``e``的类型``T``。这就指导Lean的繁饰器在试图解决隐式参数时使用值``T``作为``e``的类型。在下面的第二个例子中，这种机制用于指定表达式``id``和``List.nil``所需的类型:

```lean
#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat
```

<!--
Numerals are overloaded in Lean, but when the type of a numeral cannot
be inferred, Lean assumes, by default, that it is a natural number. So
the expressions in the first two ``#check`` commands below are
elaborated in the same way, whereas the third ``#check`` command
interprets ``2`` as an integer.
-->

Lean中数字是重载的，但是当数字的类型不能被推断时，Lean默认假设它是一个自然数。因此，下面的前两个``#check``命令中的表达式以同样的方式进行了繁饰，而第三个``#check``命令将``2``解释为整数。

```lean
#check 2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int
```

<!--
Sometimes, however, we may find ourselves in a situation where we have
declared an argument to a function to be implicit, but now want to
provide the argument explicitly. If ``foo`` is such a function, the
notation ``@foo`` denotes the same function with all the arguments
made explicit.
-->

然而，有时我们可能会发现自己处于这样一种情况：我们已经声明了函数的参数是隐式的，但现在想显式地提供参数。如果``foo``是有隐参数的函数，符号``@foo``表示所有参数都是显式的该函数。

```lean
#check @id        -- {α : Sort u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool
```

第一个``#check``命令给出了标识符的类型``id``，没有插入任何占位符。而且，输出表明第一个参数是隐式的。
