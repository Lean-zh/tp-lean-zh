<!--
Interacting with Lean
=====================
-->

与 Lean 交互
=====================

<!--
You are now familiar with the fundamentals of dependent type theory,
both as a language for defining mathematical objects and a language
for constructing proofs. The one thing you are missing is a mechanism
for defining new data types. We will fill this gap in the next
chapter, which introduces the notion of an *inductive data type*. But
first, in this chapter, we take a break from the mechanics of type
theory to explore some pragmatic aspects of interacting with Lean.

Not all of the information found here will be useful to you right
away. We recommend skimming this section to get a sense of Lean's
features, and then returning to it as necessary.
-->

你现在已经熟悉了依值类型论的基本原理，它既是一种定义数学对象的语言，也是一种构造证明的语言。现在你缺少一个定义新数据类型的机制。下一章介绍*归纳数据类型*的概念来帮你完成这个目标。但首先，在这一章中，我们从类型论的机制中抽身出来，探索与 Lean 交互的一些实用性问题。

并非所有的知识都能马上对你有用。可以略过这一节，然后在必要时再回到这一节以了解 Lean 的特性。

<!--
Importing Files
---------------
-->

导入文件
---------------

<!--
The goal of Lean's front end is to interpret user input, construct
formal expressions, and check that they are well formed and type
correct. Lean also supports the use of various editors, which provide
continuous checking and feedback. More information can be found on the
Lean [documentation pages](https://lean-lang.org/documentation/).

The definitions and theorems in Lean's standard library are spread
across multiple files. Users may also wish to make use of additional
libraries, or develop their own projects across multiple files. When
Lean starts, it automatically imports the contents of the library
``Init`` folder, which includes a number of fundamental definitions
and constructions. As a result, most of the examples we present here
work "out of the box."

If you want to use additional files, however, they need to be imported
manually, via an ``import`` statement at the beginning of a file. The
command
-->

Lean的前端的目标是解释用户的输入，构建形式化的表达式，并检查它们是否形式良好和类型正确。Lean还支持使用各种编辑器，这些编辑器提供持续的检查和反馈。更多信息可以在Lean[文档](https://lean-lang.org/documentation/)上找到。

Lean的标准库中的定义和定理分布在多个文件中。用户也可能希望使用额外的库，或在多个文件中开发自己的项目。当 Lean 启动时，它会自动导入库中 `Init` 文件夹的内容，其中包括一些基本定义和结构。因此，我们在这里介绍的大多数例子都是「开箱即用」的。

然而，如果你想使用其他文件，需要通过文件开头的`import'语句手动导入。命令

```
import Bar.Baz.Blah
```

<!--
imports the file ``Bar/Baz/Blah.olean``, where the descriptions are
interpreted relative to the Lean *search path*. Information as to how
the search path is determined can be found on the
[documentation pages](https://lean-lang.org/documentation/).
By default, it includes the standard library directory, and (in some contexts)
the root of the user's local project.

Importing is transitive. In other words, if you import ``Foo`` and ``Foo`` imports ``Bar``,
then you also have access to the contents of ``Bar``, and do not need to import it explicitly.
-->

导入文件 ``Bar/Baz/Blah.olean``，其中的描述是相对于Lean**搜索路径**解释的。关于如何确定搜索路径的信息可以在[文档](https://lean-lang.org/documentation/)中找到。默认情况下，它包括标准库目录，以及（在某些情况下）用户的本地项目的根目录。

导入是传递性的。换句话说，如果你导入了 ``Foo``，并且 ``Foo`` 导入了 ``Bar``，那么你也可以访问 ``Bar`` 的内容，而不需要明确导入它。

<!--
More on Sections
----------------
-->

小节（续）
----------------

<!--
Lean provides various sectioning mechanisms to help structure a
theory. You saw in [Variables and Sections](./dependent_type_theory.md#variables-and-sections) that the
``section`` command makes it possible not only to group together
elements of a theory that go together, but also to declare variables
that are inserted as arguments to theorems and definitions, as
necessary. Remember that the point of the `variable` command is to
declare variables for use in theorems, as in the following example:
-->

Lean提供了各种分段机制来帮助构造理论。你在[变量和小节](./dependent_type_theory.md#变量和小节)中看到，``section`` 命令不仅可以将理论中的元素组合在一起，还可以在必要时声明变量，作为定理和定义的参数插入。请记住，`variable` 命令的意义在于声明变量，以便在定理中使用，如下面的例子：

```lean
section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end
```

<!--
The definition of ``double`` does not have to declare ``x`` as an
argument; Lean detects the dependence and inserts it
automatically. Similarly, Lean detects the occurrence of ``x`` in
``t1`` and ``t2``, and inserts it automatically there, too.
Note that ``double`` does *not* have ``y`` as argument. Variables are only
included in declarations where they are actually used.
-->

``double`` 的定义不需要声明 ``x`` 作为参数；Lean检测到这种依赖关系并自动插入。同样，Lean检测到 ``x`` 在 ``t1`` 和 ``t2`` 中的出现，也会自动插入。注意，double**没有**``y`` 作为参数。变量只包括在实际使用的声明中。

<!--
More on Namespaces
------------------
-->

命名空间（续）
------------------

<!--
In Lean, identifiers are given by hierarchical *names* like
``Foo.Bar.baz``. We saw in [Namespaces](./dependent_type_theory.md#namespaces) that Lean provides
mechanisms for working with hierarchical names. The command
``namespace foo`` causes ``foo`` to be prepended to the name of each
definition and theorem until ``end foo`` is encountered. The command
``open foo`` then creates temporary *aliases* to definitions and
theorems that begin with prefix ``foo``.
-->

在 Lean 中，标识符是由层次化的*名称*给出的，如 ``Foo.Bar.baz``。我们在[命名空间](./dependent_type_theory.md#命名空间)一节中看到，Lean提供了处理分层名称的机制。命令 ``namespace foo`` 导致 ``foo`` 被添加到每个定义和定理的名称中，直到遇到 ``end foo``。命令 ``open foo`` 然后为以 `foo` 开头的定义和定理创建临时的**别名**。

```lean
namespace Foo
def bar : Nat := 1
end Foo

open Foo

#check bar
#check Foo.bar
```

<!--
The following definition
-->

下面的定义

```lean
def Foo.bar : Nat := 1
```

<!--
is treated as a macro, and expands to
-->

被看成一个宏；展开成

```lean
namespace Foo
def bar : Nat := 1
end Foo
```

<!--
Although the names of theorems and definitions have to be unique, the
aliases that identify them do not. When we open a namespace, an
identifier may be ambiguous. Lean tries to use type information to
disambiguate the meaning in context, but you can always disambiguate
by giving the full name. To that end, the string ``_root_`` is an
explicit description of the empty prefix.
-->

尽管定理和定义的名称必须是唯一的，但标识它们的别名却不是。当我们打开一个命名空间时，一个标识符可能是模糊的。Lean试图使用类型信息来消除上下文中的含义，但你总是可以通过给出全名来消除歧义。为此，字符串 ``_root_`` 是对空前缀的明确表述。

```lean
def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String
-- #check add -- ambiguous
#check String.add           -- String → String → String
#check Bool.add             -- Bool → Bool → Bool
#check _root_.add           -- Type → Type → Type

#check add "hello" "world"  -- String
#check add true false       -- Bool
#check add Nat Nat          -- Type
```

<!--
We can prevent the shorter alias from being created by using the ``protected`` keyword:
-->

我们可以通过使用 ``protected`` 关键字来阻止创建较短的别名：

```lean
protected def Foo.bar : Nat := 1

open Foo

-- #check bar -- error
#check Foo.bar
```

<!--
This is often used for names like ``Nat.rec`` and ``Nat.recOn``, to prevent
overloading of common names.

The ``open`` command admits variations. The command
-->

这通常用于像`Nat.rec`和`Nat.recOn`这样的名称，以防止普通名称的重载。

``open`` 命令允许变量。命令

```lean
open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3
```

<!--
creates aliases for only the identifiers listed. The command
-->

仅对列出的标识符创建了别名。命令

```lean
open Nat hiding succ gcd
#check zero     -- Nat
-- #eval gcd 15 6  -- error
#eval Nat.gcd 15 6  -- 3
```

<!--
creates aliases for everything in the ``Nat`` namespace *except* the identifiers listed.
-->

给 ``Nat`` 命名空间中**除了**被列出的标识符都创建了别名。命令

```lean
open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3  -- 7
```

<!--
creates aliases renaming ``Nat.mul`` to ``times`` and ``Nat.add`` to ``plus``.

It is sometimes useful to ``export`` aliases from one namespace to another, or to the top level. The command
-->

将`Nat.mul`更名为 `times`，`Nat.add`更名为 `plus`。

有时，将别名从一个命名空间导出到另一个命名空间，或者导出到上一层是很有用的。命令

```lean
export Nat (succ add sub)
```

<!--
creates aliases for ``succ``, ``add``, and ``sub`` in the current
namespace, so that whenever the namespace is open, these aliases are
available. If this command is used outside a namespace, the aliases
are exported to the top level.
-->

在当前命名空间中为 ``succ``、``add`` 和 ``sub`` 创建别名，这样无论何时命名空间被打开，这些别名都可以使用。如果这个命令在名字空间之外使用，那么这些别名会被输出到上一层。

<!--
Attributes
----------
-->

属性
----------

<!--
The main function of Lean is to translate user input to formal
expressions that are checked by the kernel for correctness and then
stored in the environment for later use. But some commands have other
effects on the environment, either assigning attributes to objects in
the environment, defining notation, or declaring instances of type
classes, as described in [Chapter Type Classes](./type_classes.md). Most of
these commands have global effects, which is to say, that they remain
in effect not only in the current file, but also in any file that
imports it. However, such commands often support the ``local`` modifier,
which indicates that they only have effect until
the current ``section`` or ``namespace`` is closed, or until the end
of the current file.

In [Section Using the Simplifier](./tactics.md#using-the-simplifier),
we saw that theorems can be annotated with the ``[simp]`` attribute,
which makes them available for use by the simplifier.
The following example defines the prefix relation on lists,
proves that this relation is reflexive, and assigns the ``[simp]`` attribute to that theorem.
-->

Lean的主要功能是把用户的输入翻译成形式化的表达式，由内核检查其正确性，然后存储在环境中供以后使用。但是有些命令对环境有其他的影响，或者给环境中的对象分配属性，定义符号，或者声明类型族的实例，如[类型族](./type_classes.md)一章所述。这些命令大多具有全局效应，也就是说，它们不仅在当前文件中保持有效，而且在任何导入它的文件中也保持有效。然而，这类命令通常支持 ``local`` 修饰符，这表明它们只在当前 ``section`` 或 ``namespace`` 关闭前或当前文件结束前有效。

在[简化](./tactics.md#简化)一节中，我们看到可以用`[simp]`属性来注释定理，这使它们可以被简化器使用。下面的例子定义了列表的前缀关系，证明了这种关系是自反的，并为该定理分配了`[simp]`属性。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

<!--
The simplifier then proves ``isPrefix [1, 2, 3] [1, 2, 3]`` by rewriting it to ``True``.

One can also assign the attribute any time after the definition takes place:
-->

然后简化器通过将其改写为 ``True`` 来证明 ``isPrefix [1, 2, 3] [1, 2, 3]``。

你也可以在做出定义后的任何时候分配属性：

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self
```

<!--
In all these cases, the attribute remains in effect in any file that
imports the one in which the declaration occurs. Adding the ``local``
modifier restricts the scope:
-->

在所有这些情况下，该属性在任何导入该声明的文件中仍然有效。添加 ``local`` 修饰符可以限制范围：

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#  ∃ t, l₁ ++ t = l₂
section

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

-- Error:
-- example : isPrefix [1, 2, 3] [1, 2, 3] := by
--  simp
```

<!--
For another example, we can use the ``instance`` command to assign the
notation ``≤`` to the `isPrefix` relation. That command, which will
be explained in [Chapter Type Classes](./type_classes.md), works by
assigning an ``[instance]`` attribute to the associated definition.
-->

另一个例子，我们可以使用 `instance` 命令来给 `isPrefix` 关系分配符号`≤`。该命令将在[类型族](./type_classes.md)中解释，它的工作原理是给相关定义分配一个`[instance]`属性。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_self (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

<!--
That assignment can also be made local:
-->

这个分配也可以是局部的：

```lean
# def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
#   ∃ t, l₁ ++ t = l₂
def instLe : LE (List α) :=
  { le := isPrefix }

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

-- Error:
-- example (as : List α) : as ≤ as :=
--  ⟨[], by simp⟩
```

<!--
In [Section Notation](#notation) below, we will discuss Lean's
mechanisms for defining notation, and see that they also support the
``local`` modifier. However, in [Section Setting Options](#setting-options), we will
discuss Lean's mechanisms for setting options, which does *not* follow
this pattern: options can *only* be set locally, which is to say,
their scope is always restricted to the current section or current
file.
-->

在下面的[符号](#符号)一节中，我们将讨论 Lean 定义符号的机制，并看到它们也支持 ``local`` 修饰符。然而，在[设置选项](#设置选项)一节中，我们将讨论 Lean 设置选项的机制，它并**不**遵循这种模式：选项**只能**在局部设置，也就是说，它们的范围总是限制在当前小节或当前文件中。

<!--
More on Implicit Arguments
--------------------------
-->

隐参数（续）
--------------------------

<!--
In [Section Implicit Arguments](./dependent_type_theory.md#implicit-arguments),
we saw that if Lean displays the type
of a term ``t`` as ``{x : α} → β x``, then the curly brackets
indicate that ``x`` has been marked as an *implicit argument* to
``t``. This means that whenever you write ``t``, a placeholder, or
"hole," is inserted, so that ``t`` is replaced by ``@t _``. If you
don't want that to happen, you have to write ``@t`` instead.

Notice that implicit arguments are inserted eagerly. Suppose we define
a function ``f (x : Nat) {y : Nat} (z : Nat)`` with the arguments
shown. Then, when we write the expression ``f 7`` without further
arguments, it is parsed as ``f 7 _``. Lean offers a weaker annotation,
``{{y : Nat}}``, which specifies that a placeholder should only be added
*before* a subsequent explicit argument. This annotation can also be
written using as ``⦃y : Nat⦄``, where the unicode brackets are entered
as ``\{{`` and ``\}}``, respectively. With this annotation, the
expression ``f 7`` would be parsed as is, whereas ``f 7 3`` would be
parsed as ``f 7 _ 3``, just as it would be with the strong annotation.

To illustrate the difference, consider the following example, which
shows that a reflexive euclidean relation is both symmetric and
transitive.
-->

在[隐参数](./dependent_type_theory.md#隐参数)一节中，我们看到，如果 Lean 将术语 ``t`` 的类型显示为 ``{x : α} → β x``，那么大括号表示 ``x`` 被标记为 ``t`` 的*隐参数*。这意味着每当你写 ``t`` 时，就会插入一个占位符，或者说「洞」，这样 ``t`` 就会被 ``@t _`` 取代。如果你不希望这种情况发生，你必须写 ``@t`` 来代替。

请注意，隐参数是急于插入的。假设我们定义一个函数 ``f (x : Nat) {y : Nat} (z : Nat)``。那么，当我们写表达式`f 7`时，没有进一步的参数，它会被解析为`f 7 _`。Lean提供了一个较弱的注释，``{{y : ℕ}}``，它指定了一个占位符只应在后一个显式参数之前添加。这个注释也可以写成 ``⦃y : Nat⦄``，其中的 unicode 括号输入方式为 ``\{{`` 和 ``\}}``。有了这个注释，表达式`f 7`将被解析为原样，而`f 7 3`将被解析为 ``f 7 _ 3``，就像使用强注释一样。

为了说明这种区别，请看下面的例子，它表明一个自反的欧几里得关系既是对称的又是传递的。

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
 th2 (th1 reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- r ?m1 ?m2 → r ?m1 ?m3 → r ?m2 ?m3
```

<!--
The results are broken down into small steps: ``th1`` shows that a
relation that is reflexive and euclidean is symmetric, and ``th2``
shows that a relation that is symmetric and euclidean is
transitive. Then ``th3`` combines the two results. But notice that we
have to manually disable the implicit arguments in ``euclr``, because
otherwise too many implicit arguments are inserted. The problem goes
away if we use weak implicit arguments:
-->

这些结果被分解成几个小步骤。``th1`` 表明自反和欧氏的关系是对称的，``th2`` 表明对称和欧氏的关系是传递的。然后 ``th3`` 结合这两个结果。但是请注意，我们必须手动禁用 `th1`、`th2` 和 `euclr` 中的隐参数，否则会插入太多的隐参数。如果我们使用弱隐式参数，这个问题就会消失：

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : euclidean r)
            : transitive r :=
  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check euclr  -- euclidean r
```

<!--
There is a third kind of implicit argument that is denoted with square
brackets, ``[`` and ``]``. These are used for type classes, as
explained in [Chapter Type Classes](./type_classes.md).
-->

还有第三种隐式参数，用方括号表示，``[`` 和 ``]``。这些是用于类型族的，在[类型族](./type_classes.md)中解释。

<!--
Notation
--------
-->

符号
--------

<!--
Identifiers in Lean can include any alphanumeric characters, including
Greek characters (other than ∀ , Σ , and λ , which, as we have seen,
have a special meaning in the dependent type theory). They can also
include subscripts, which can be entered by typing ``\_`` followed by
the desired subscripted character.

Lean's parser is extensible, which is to say, we can define new notation.

Lean's syntax can be extended and customized by users at every level,
ranging from basic "mixfix" notations to custom elaborators.  In fact,
all builtin syntax is parsed and processed using the same mechanisms
and APIs open to users.  In this section, we will describe and explain
the various extension points.

While introducing new notations is a relatively rare feature in
programming languages and sometimes even frowned upon because of its
potential to obscure code, it is an invaluable tool in formalization
for expressing established conventions and notations of the respective
field succinctly in code.  Going beyond basic notations, Lean's
ability to factor out common boilerplate code into (well-behaved)
macros and to embed entire custom domain specific languages (DSLs) to
textually encode subproblems efficiently and readably can be of great
benefit to both programmers and proof engineers alike.
-->

Lean中的标识符可以包括任何字母数字字符，包括希腊字母（除了∀、Σ和λ，它们在依值类型论中有特殊的含义）。它们还可以包括下标，可以通过输入 ``\_``，然后再输入所需的下标字符。

Lean的解析器是可扩展的，也就是说，我们可以定义新的符号。

Lean的语法可以由用户在各个层面进行扩展和定制，从基本的「mixfix」符号到自定义的繁饰器。事实上，所有内置的语法都是使用对用户开放的相同机制和 API 进行解析和处理的。 在本节中，我们将描述和解释各种扩展点。

虽然在编程语言中引入新的符号是一个相对罕见的功能，有时甚至因为它有可能使代码变得模糊不清而被人诟病，但它是形式化的一个宝贵工具，可以在代码中简洁地表达各自领域的既定惯例和符号。 除了基本的符号之外，Lean的能力是将普通的样板代码分解成（良好的）宏，并嵌入整个定制的特定领域语言（DSL，domain specific language），对子问题进行高效和可读的文本编码，这对程序员和证明工程师都有很大的好处。

<!--
### Notations and Precedence
-->

### 符号和优先级

<!--
The most basic syntax extension commands allow introducing new (or
overloading existing) prefix, infix, and postfix operators.
-->

最基本的语法扩展命令允许引入新的（或重载现有的）前缀、下缀和后缀运算符：

<!--
```lean
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
# set_option quotPrecheck false
postfix:max "⁻¹"  => Inv.inv
```
-->

```lean
infixl:65   " + " => HAdd.hAdd  -- 左结合
infix:50    " = " => Eq         -- 非结合
infixr:80   " ^ " => HPow.hPow  -- 右结合
prefix:100  "-"   => Neg.neg
set_option quotPrecheck false
postfix:max "⁻¹"  => Inv.inv
```

<!--
After the initial command name describing the operator kind (its
"fixity"), we give the *parsing precedence* of the operator preceded
by a colon `:`, then a new or existing token surrounded by double
quotes (the whitespace is used for pretty printing), then the function
this operator should be translated to after the arrow `=>`.

The precedence is a natural number describing how "tightly" an
operator binds to its arguments, encoding the order of operations.  We
can make this more precise by looking at the commands the above unfold to:
-->

语法：

运算符种类（其「结合方式」） : 解析优先级 " 新的或现有的符号 " => 这个符号应该翻译成的函数

优先级是一个自然数，描述一个运算符与它的参数结合的「紧密程度」，编码操作的顺序。我们可以通过查看上述展开的命令来使之更加精确：

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
# set_option quotPrecheck false
notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- `max` is a shorthand for precedence 1024
```

<!--
It turns out that all commands from the first code block are in fact
command *macros* translating to the more general `notation` command.
We will learn about writing such macros below.  Instead of a single
token, the `notation` command accepts a mixed sequence of tokens and
named term placeholders with precedences, which can be referenced on
the right-hand side of `=>` and will be replaced by the respective
term parsed at that position.  A placeholder with precedence `p`
accepts only notations with precedence at least `p` in that place.
Thus the string `a + b + c` cannot be parsed as the equivalent of
`a + (b + c)` because the right-hand side operand of an `infixl` notation
has precedence one greater than the notation itself.  In contrast,
`infixr` reuses the notation's precedence for the right-hand side
operand, so `a ^ b ^ c` *can* be parsed as `a ^ (b ^ c)`.  Note that
if we used `notation` directly to introduce an infix notation like
-->

事实证明，第一个代码块中的所有命令实际上都是命令**宏**，翻译成更通用的 `notation` 命令。我们将在下面学习如何编写这种宏。 `notation` 命令不接受单一的记号，而是接受一个混合的记号序列和有优先级的命名项占位符，这些占位符可以在`=>`的右侧被引用，并将被在该位置解析的相应项所取代。 优先级为 `p` 的占位符在该处只接受优先级至少为 `p` 的记号。因此，字符串`a + b + c`不能被解析为等同于`a + (b + c)`，因为 `infixl` 符号的右侧操作数的优先级比该符号本身大。 相反，`infixr` 重用了符号右侧操作数的优先级，所以`a ^ b ^ c` *可以*被解析为`a ^ (b ^ c)`。 注意，如果我们直接使用 `notation` 来引入一个 infix 符号，如

```lean
# set_option quotPrecheck false
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

<!--
where the precedences do not sufficiently determine associativity,
Lean's parser will default to right associativity.  More precisely,
Lean's parser follows a local *longest parse* rule in the presence of
ambiguous grammars: when parsing the right-hand side of `a ~` in
`a ~ b ~ c`, it will continue parsing as long as possible (as the current
precedence allows), not stopping after `b` but parsing `~ c` as well.
Thus the term is equivalent to `a ~ (b ~ c)`.

As mentioned above, the `notation` command allows us to define
arbitrary *mixfix* syntax freely mixing tokens and placeholders.
-->

在上文没有充分确定结合规则的情况下，Lean的解析器将默认为右结合。 更确切地说，Lean的解析器在存在模糊语法的情况下遵循一个局部的*最长解析*规则：当解析`a ~`中`a ~ b ~ c`的右侧时，它将继续尽可能长的解析（在当前的上下文允许的情况下），不在 `b` 之后停止，而是同时解析`~ c`。因此该术语等同于`a ~ (b ~ c)`。

如上所述，`notation` 命令允许我们定义任意的*mixfix*语法，自由地混合记号和占位符。

```lean
# set_option quotPrecheck false
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

<!--
Placeholders without precedence default to `0`, i.e. they accept notations of any precedence in their place.
If two notations overlap, we again apply the longest parse rule:
-->

没有优先级的占位符默认为 `0`，也就是说，它们接受任何优先级的符号来代替它们。如果两个记号重叠，我们再次应用最长解析规则：

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

<!--
The new notation is preferred to the binary notation since the latter,
before chaining, would stop parsing after `1 + 2`.  If there are
multiple notations accepting the same longest parse, the choice will
be delayed until elaboration, which will fail unless exactly one
overload is type correct.
-->

新的符号比二进制符号要好，因为后者在连锁之前，会在`1 + 2`之后停止解析。 如果有多个符号接受同一个最长的解析，选择将被推迟到阐述，这将失败，除非正好有一个重载是类型正确的。

<!--
Coercions
---------
-->

强制转换
---------

<!--
In Lean, the type of natural numbers, ``Nat``, is different from the
type of integers, ``Int``. But there is a function ``Int.ofNat`` that
embeds the natural numbers in the integers, meaning that we can view
any natural number as an integer, when needed. Lean has mechanisms to
detect and insert *coercions* of this sort.
-->

在 Lean 中，自然数的类型 ``Nat``，与整数的类型 ``Int`` 不同。但是有一个函数 ``Int.ofNat`` 将自然数嵌入整数中，这意味着我们可以在需要时将任何自然数视为整数。Lean有机制来检测和插入这种**强制转换**。

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int
```

<!--
Displaying Information
----------------------
-->

显示信息
----------------------

<!--
There are a number of ways in which you can query Lean for information
about its current state and the objects and theorems that are
available in the current context. You have already seen two of the
most common ones, ``#check`` and ``#eval``. Remember that ``#check``
is often used in conjunction with the ``@`` operator, which makes all
of the arguments to a theorem or definition explicit. In addition, you
can use the ``#print`` command to get information about any
identifier. If the identifier denotes a definition or theorem, Lean
prints the type of the symbol, and its definition. If it is a constant
or an axiom, Lean indicates that fact, and shows the type.
-->

有很多方法可以让你查询 Lean 的当前状态以及当前上下文中可用的对象和定理的信息。你已经看到了两个最常见的方法，`#check`和`#eval`。请记住，`#check`经常与`@`操作符一起使用，它使定理或定义的所有参数显式化。此外，你可以使用`#print`命令来获得任何标识符的信息。如果标识符表示一个定义或定理，Lean会打印出符号的类型，以及它的定义。如果它是一个常数或公理，Lean会指出它并显示其类型。

<!--
```lean
-- examples with equality
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

-- examples with And
#check And
#check And.intro
#check @And.intro

-- a user-defined function
def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo
```
-->

```lean
-- 等式
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

-- 与
#check And
#check And.intro
#check @And.intro

-- 自定义函数
def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo
```

<!--
Setting Options
---------------
-->

设置选项
---------------

<!--
Lean maintains a number of internal variables that can be set by users
to control its behavior. The syntax for doing so is as follows:
-->

Lean维护着一些内部变量，用户可以通过设置这些变量来控制其行为。语法如下：

```
set_option <name> <value>
```

<!--
One very useful family of options controls the way Lean's *pretty- printer* displays terms. The following options take an input of true or false:
-->

有一系列非常有用的选项可以控制 Lean 的**美观打印**显示项的方式。下列选项的输入值为真或假：

```
pp.explicit  : display implicit arguments
pp.universes : display hidden universe parameters
pp.notation  : display output using defined notations
```

<!--
As an example, the following settings yield much longer output:
-->

例如，以下设置会产生更长的输出:

```lean
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1
```

<!--
The command ``set_option pp.all true`` carries out these settings all
at once, whereas ``set_option pp.all false`` reverts to the previous
values. Pretty printing additional information is often very useful
when you are debugging a proof, or trying to understand a cryptic
error message. Too much information can be overwhelming, though, and
Lean's defaults are generally sufficient for ordinary interactions.
-->

命令 ``set_option pp.all true`` 一次性执行这些设置，而 ``set_option pp.all false`` 则恢复到之前的值。当你调试一个证明，或试图理解一个神秘的错误信息时，漂亮地打印额外的信息往往是非常有用的。不过太多的信息可能会让人不知所措，Lean的默认值一般来说对普通的交互是足够的。

<!--
Elaboration Hints
-----------------

When you ask Lean to process an expression like ``λ x y z, f (x + y) z``, you are leaving information implicit. For example, the types of ``x``, ``y``, and ``z`` have to be inferred from the context, the notation ``+`` may be overloaded, and there may be implicit arguments to ``f`` that need to be filled in as well. Moreover, we will see in :numref:`Chapter %s <type_classes>` that some implicit arguments are synthesized by a process known as *type class resolution*. And we have also already seen in the last chapter that some parts of an expression can be constructed by the tactic framework.

Inferring some implicit arguments is straightforward. For example, suppose a function ``f`` has type ``Π {α : Type*}, α → α → α`` and Lean is trying to parse the expression ``f n``, where ``n`` can be inferred to have type ``nat``. Then it is clear that the implicit argument ``α`` has to be ``nat``. However, some inference problems are *higher order*. For example, the substitution operation for equality, ``eq.subst``, has the following type:

.. code-block:: text

    eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α},
                 a = b → p a → p b

Now suppose we are given ``a b : ℕ`` and ``h₁ : a = b`` and ``h₂ : a * b > a``. Then, in the expression ``eq.subst h₁ h₂``, ``P`` could be any of the following:

-  ``λ x, x * b > x``
-  ``λ x, x * b > a``
-  ``λ x, a * b > x``
-  ``λ x, a * b > a``

In other words, our intent may be to replace either the first or second ``a`` in ``h₂``, or both, or neither. Similar ambiguities arise in inferring induction predicates, or inferring function arguments. Even second-order unification is known to be undecidable. Lean therefore relies on heuristics to fill in such arguments, and when it fails to guess the right ones, they need to be provided explicitly.

To make matters worse, sometimes definitions need to be unfolded, and sometimes expressions need to be reduced according to the computational rules of the underlying logical framework. Once again, Lean has to rely on heuristics to determine what to unfold or reduce, and when.

There are attributes, however, that can be used to provide hints to the elaborator. One class of attributes determines how eagerly definitions are unfolded: constants can be marked with the attribute ``[reducible]``, ``[semireducible]``, or ``[irreducible]``. Definitions are marked ``[semireducible]`` by default. A definition with the ``[reducible]`` attribute is unfolded eagerly; if you think of a definition as serving as an abbreviation, this attribute would be appropriate. The elaborator avoids unfolding definitions with the ``[irreducible]`` attribute. Theorems are marked ``[irreducible]`` by default, because typically proofs are not relevant to the elaboration process.

It is worth emphasizing that these attributes are only hints to the elaborator. When checking an elaborated term for correctness, Lean's kernel will unfold whatever definitions it needs to unfold. As with other attributes, the ones above can be assigned with the ``local`` modifier, so that they are in effect only in the current section or file.

Lean also has a family of attributes that control the elaboration strategy. A definition or theorem can be marked ``[elab_with_expected_type]``, ``[elab_simple]``. or ``[elab_as_eliminator]``. When applied to a definition ``f``, these bear on elaboration of an expression ``f a b c ...`` in which ``f`` is applied to arguments. With the default attribute, ``[elab_with_expected_type]``, the arguments ``a``, ``b``, ``c``, ... are elaborating using information about their expected type, inferred from ``f`` and the previous arguments. In contrast, with ``[elab_simple]``, the arguments are elaborated from left to right without propagating information about their types. The last attribute, ``[elab_as_eliminator]``, is commonly used for eliminators like recursors, induction principles, and ``eq.subst``. It uses a separate heuristic to infer higher-order parameters. We will consider such operations in more detail in the next chapter.

Once again, these attributes can be assigned and reassigned after an object is defined, and you can use the ``local`` modifier to limit their scope. Moreover, using the ``@`` symbol in front of an identifier in an expression instructs the elaborator to use the ``[elab_simple]`` strategy; the idea is that, when you provide the tricky parameters explicitly, you want the elaborator to weigh that information heavily. In fact, Lean offers an alternative annotation, ``@@``, which leaves parameters before the first higher-order parameter implicit. For example, ``@@eq.subst`` leaves the type of the equation implicit, but makes the context of the substitution explicit.

-->

<!--
Using the Library
-----------------
-->

使用库
-----------------

<!--
To use Lean effectively you will inevitably need to make use of
definitions and theorems in the library. Recall that the ``import``
command at the beginning of a file imports previously compiled results
from other files, and that importing is transitive; if you import
``Foo`` and ``Foo`` imports ``Bar``, then the definitions and theorems
from ``Bar`` are available to you as well. But the act of opening a
namespace, which provides shorter names, does not carry over. In each
file, you need to open the namespaces you wish to use.

In general, it is important for you to be familiar with the library
and its contents, so you know what theorems, definitions, notations,
and resources are available to you. Below we will see that Lean's
editor modes can also help you find things you need, but studying the
contents of the library directly is often unavoidable. Lean's standard
library can be found online, on GitHub:
-->

为了有效地使用Lean，你将不可避免地需要使用库中的定义和定理。回想一下，文件开头的 ``import`` 命令会从其他文件中导入之前编译的结果，而且导入是传递的；如果你导入了 ``Foo``，``Foo`` 又导入了 ``Bar``，那么 ``Bar`` 的定义和定理也可以被你利用。但是打开一个命名空间的行为，提供了更短的名字，并没有延续下去。在每个文件中，你需要打开你想使用的命名空间。

一般来说，你必须熟悉库和它的内容，这样你就知道有哪些定理、定义、符号和资源可供你使用。下面我们将看到 Lean 的编辑器模式也可以帮助你找到你需要的东西，但直接研究库的内容往往是不可避免的。Lean的标准库在 GitHub 上。

- [https://github.com/leanprover/lean4/tree/master/src/Init](https://github.com/leanprover/lean4/tree/master/src/Init)

- [https://github.com/leanprover/std4/tree/main/Std](https://github.com/leanprover/std4/tree/main/Std)

<!--
You can see the contents of these directories and files using GitHub's
browser interface. If you have installed Lean on your own computer,
you can find the library in the ``lean`` folder, and explore it with
your file manager. Comment headers at the top of each file provide
additional information.

Lean's library developers follow general naming guidelines to make it
easier to guess the name of a theorem you need, or to find it using
tab completion in editors with a Lean mode that supports this, which
is discussed in the next section. Identifiers are generally
``camelCase``, and types are `CamelCase`. For theorem names,
we rely on descriptive names where the different components are separated
by `_`s. Often the name of theorem simply describes the conclusion:
-->

你可以使用 GitHub 的浏览器界面查看这些目录和文件的内容。如果你在自己的电脑上安装了Lean，你可以在 ``lean`` 文件夹中找到这个库，用你的文件管理器探索它。每个文件顶部的注释标题提供了额外的信息。

Lean库的开发者遵循一般的命名准则，以便于猜测你所需要的定理的名称，或者在支持 Lean 模式的编辑器中用 Tab 自动补全来找到它，这将在下一节讨论。标识符一般是 ``camelCase``，而类型是 `CamelCase`。对于定理的名称，我们依靠描述性的名称，其中不同的组成部分用 `_` 分开。通常情况下，定理的名称只是描述结论。

```lean
#check Nat.succ_ne_zero
#check Nat.zero_add
#check Nat.mul_one
#check Nat.le_of_succ_le_succ
```

<!--
Remember that identifiers in Lean can be organized into hierarchical
namespaces. For example, the theorem named ``le_of_succ_le_succ`` in the
namespace ``Nat`` has full name ``Nat.le_of_succ_le_succ``, but the shorter
name is made available by the command ``open Nat`` (for names not marked as
`protected`). We will see in [Chapter Inductive Types](./inductive_types.md)
and [Chapter Structures and Records](./structures_and_records.md)
that defining structures and inductive data types in Lean generates
associated operations, and these are stored in
a namespace with the same name as the type under definition. For
example, the product type comes with the following operations:
-->

Lean中的标识符可以被组织到分层的命名空间中。例如，命名空间 ``Nat`` 中名为 ``le_of_succ_le_succ`` 的定理有全称 ``Nat.le_of_succ_le_succ``，但较短的名称可由命令 ``open Nat`` 提供（对于未标记为 `protected` 的名称）。我们将在[归纳类型](./inductive_types.md)和[结构体和记录](./structures_and_records.md)中看到，在 Lean 中定义结构体和归纳数据类型会产生相关操作，这些操作存储在与被定义类型同名的命名空间。例如，乘积类型带有以下操作：

```lean
#check @Prod.mk
#check @Prod.fst
#check @Prod.snd
#check @Prod.rec
```

<!--
The first is used to construct a pair, whereas the next two,
``Prod.fst`` and ``Prod.snd``, project the two elements. The last,
``Prod.rec``, provides another mechanism for defining functions on a
product in terms of a function on the two components. Names like
``Prod.rec`` are *protected*, which means that one has to use the full
name even when the ``Prod`` namespace is open.

With the propositions as types correspondence, logical connectives are
also instances of inductive types, and so we tend to use dot notation
for them as well:
-->

第一个用于构建一个对，而接下来的两个，``Prod.fst`` 和 ``Prod.snd``，投影两个元素。最后一个，``Prod.rec``，提供了另一种机制，用两个元素的函数来定义乘积上的函数。像 ``Prod.rec`` 这样的名字是*受保护*的，这意味着即使 ``Prod`` 名字空间是打开的，也必须使用全名。

由于命题即类型的对应原则，逻辑连接词也是归纳类型的实例，因此我们也倾向于对它们使用点符号：

```lean
#check @And.intro
#check @And.casesOn
#check @And.left
#check @And.right
#check @Or.inl
#check @Or.inr
#check @Or.elim
#check @Exists.intro
#check @Exists.elim
#check @Eq.refl
#check @Eq.subst
```

<!--
Auto Bound Implicit Arguments
-----------------
-->

自动约束隐参数
-----------------

<!--
In the previous section, we have shown how implicit arguments make functions more convenient to use.
However, functions such as `compose` are still quite verbose to define. Note that the universe
polymorphic `compose` is even more verbose than the one previously defined.
-->

在上一节中，我们已经展示了隐参数是如何使函数更方便使用的。然而，像 `compose` 这样的函数在定义时仍然相当冗长。宇宙多态的 `compose` 比之前定义的函数还要啰嗦。

```lean
universe u v w
def compose {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

<!--
You can avoid the `universe` command by providing the universe parameters when defining `compose`.
-->

你可以通过在定义 `compose` 时提供宇宙参数来避免使用 `universe` 命令。

```lean
def compose.{u, v, w}
            {α : Type u} {β : Type v} {γ : Type w}
            (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

<!--
Lean 4 supports a new feature called *auto bound implicit arguments*. It makes functions such as
`compose` much more convenient to write. When Lean processes the header of a declaration,
any unbound identifier is automatically added as an implicit argument *if* it is a single lower case or
greek letter. With this feature we can write `compose` as
-->

Lean 4支持一个名为**自动约束隐参数**的新特性。它使诸如 `compose` 这样的函数在编写时更加方便。当 Lean 处理一个声明的头时，**如果**它是一个小写字母或希腊字母，任何未约束的标识符都会被自动添加为隐式参数。有了这个特性，我们可以把 `compose` 写成

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```

<!--
Note that Lean inferred a more general type using `Sort` instead of `Type`.

Although we love this feature and use it extensively when implementing Lean,
we realize some users may feel uncomfortable with it. Thus, you can disable it using
the command `set_option autoImplicit false`.
-->

请注意，Lean使用 `Sort` 而不是 `Type` 推断出了一个更通用的类型。

虽然我们很喜欢这个功能，并且在实现 Lean 时广泛使用，但我们意识到有些用户可能会对它感到不舒服。因此，你可以使用`set_option autoBoundImplicitLocal false`命令将其禁用。

<!--
```lean
set_option autoImplicit false
/- The following definition produces `unknown identifier` errors -/
-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)
```
-->

```lean
set_option autoImplicit false
/- 这个定义会报错：`unknown identifier` -/
-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)
```

<!--
Implicit Lambdas
---------------
-->

隐式Lambda
---------------

<!--
In Lean 3 stdlib, we find many
[instances](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39) of the dreadful `@`+`_` idiom.
It is often used when the expected type is a function type with implicit arguments,
and we have a constant (`reader_t.pure` in the example) which also takes implicit arguments. In Lean 4, the elaborator automatically introduces lambdas
for consuming implicit arguments. We are still exploring this feature and analyzing its impact, but the experience so far has been very positive. Here is the example from the link above using Lean 4 implicit lambdas.
-->

在Lean 3 stdlib中，我们发现了许多[例子](https://github.com/leanprover/lean/blob/master/library/init/category/reader.lean#L39)包含丑陋的`@`+`_` 惯用法。当我们的预期类型是一个带有隐参数的函数类型，而我们有一个常量（例子中的`reader_t.pure`）也需要隐参数时，就会经常使用这个惯用法。在Lean 4中，繁饰器自动引入了 lambda 来消除隐参数。我们仍在探索这一功能并分析其影响，但到目前为止的结果是非常积极的。下面是上面链接中使用Lean 4隐式 lambda 的例子。

```lean
# variable (ρ : Type) (m : Type → Type) [Monad m]
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```

<!--
Users can disable the implicit lambda feature by using `@` or writing
a lambda expression with `{}` or `[]` binder annotations.  Here are
few examples
-->

用户可以通过使用`@`或用包含`{}`或`[]`的约束标记编写的 lambda 表达式来禁用隐式 lambda 功能。下面是几个例子

<!--
```lean
# namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before `fun`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
# end ex2
```
-->

```lean
# namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- 这个例子中，隐式 lambda 引入被禁用了，因为在 `fun` 前使用了`@`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- 这个例子中，隐式 lambda 引入被禁用了，因为使用了绑定记号`{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
# end ex2
```

<!--
Sugar for Simple Functions
-------------------------
-->

简单函数语法糖
-------------------------

<!--
In Lean 3, we can create simple functions from infix operators by
using parentheses. For example, `(+1)` is sugar for `fun x, x + 1`. In
Lean 4, we generalize this notation using `·` as a placeholder. Here
are a few examples:
-->

在Lean 3中，我们可以通过使用小括号从 infix 运算符中创建简单的函数。例如，`(+1)`是`fun x, x + 1`的语法糖。在Lean 4中，我们用`·`作为占位符来扩展这个符号。这里有几个例子：

```lean
# namespace ex3
#check (· + 1)
-- fun a => a + 1
#check (2 - ·)
-- fun a => 2 - a
#eval [1, 2, 3, 4, 5].foldl (·*·) 1
-- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·)
-- fun a b => f a 1 b

#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
-- [1, 3, 5]
# end ex3
```

<!--
As in Lean 3, the notation is activated using parentheses, and the lambda abstraction is created by collecting the nested `·`s.
The collection is interrupted by nested parentheses. In the following example, two different lambda expressions are created.
-->

如同在Lean 3中，符号是用圆括号激活的，lambda抽象是通过收集嵌套的`·`创建的。这个集合被嵌套的小括号打断。在下面的例子中创建了两个不同的 lambda 表达式。

```lean
#check (Prod.mk · (· + 1))
-- fun a => (a, fun b => b + 1)
```

<!--
Named Arguments
---------------
-->

命名参数
---------------

<!--
Named arguments enable you to specify an argument for a parameter by
matching the argument with its name rather than with its position in
the parameter list.  If you don't remember the order of the parameters
but know their names, you can send the arguments in any order. You may
also provide the value for an implicit parameter when Lean failed to
infer it. Named arguments also improve the readability of your code by
identifying what each argument represents.
-->

被命名参数使你可以通过用参数的名称而不是参数列表中的位置来指定参数。 如果你不记得参数的顺序但知道它们的名字，你可以以任何顺序传入参数。当 Lean 未能推断出一个隐参数时，你也可以提供该参数的值。被命名参数还可以通过识别每个参数所代表的内容来提高你的代码的可读性。

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
    : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

<!--
In the following examples, we illustrate the interaction between named
and default arguments.
-->

在下面的例子中，我们说明了被命名参数和默认参数之间的交互。

```lean
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl

example : f = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl
```

<!--
You can use `..` to provide missing explicit arguments as `_`.
This feature combined with named arguments is useful for writing patterns. Here is an example:
-->

你可以使用`..`来提供缺少的显式参数作为 `_`。这个功能与被命名参数相结合，对编写模式很有用。下面是一个例子：

```lean
inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | app    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none
```

<!--
Ellipses are also useful when explicit arguments can be automatically
inferred by Lean, and we want to avoid a sequence of `_`s.
-->

当显式参数可以由 Lean 自动推断时，省略号也很有用，而我们想避免一连串的 `_`。

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```
