import VersoManual
import TPiLZh.Examples

open Verso.Genre Manual
open TPiLZh

#doc (Manual) "与 Lean 交互" =>
%%%
tag := "interacting-with-lean"
file := "InteractingWithLean"
%%%
-- Interacting with Lean

-- You are now familiar with the fundamentals of dependent type theory,
-- both as a language for defining mathematical objects and a language
-- for constructing proofs. The one thing you are missing is a mechanism
-- for defining new data types. We will fill this gap in the next
-- chapter, which introduces the notion of an _inductive data type_. But
-- first, in this chapter, we take a break from the mechanics of type
-- theory to explore some pragmatic aspects of interacting with Lean.

你现在已经熟悉了依值类型论的基本原理，它既是一种定义数学对象的语言，也是一种构造证明的语言。
现在你缺少一个定义新数据类型的机制。下一章介绍 _归纳数据类型_ 的概念来帮你完成这个目标。
但首先，在这一章中，我们从类型论的机制中抽身出来，探索与 Lean 交互的一些实用性问题。

-- Not all of the information found here will be useful to you right
-- away. We recommend skimming this section to get a sense of Lean's
-- features, and then returning to it as necessary.

并非所有的知识都能马上对你有用。可以略过这一节，然后在必要时再回到这一节以了解 Lean 的特性。

-- # Messages
# 消息
%%%
tag := "messages"
%%%

-- Lean produces three kinds of messages:

Lean 产生三种消息：

-- : Errors

--   Errors are produced when an inconsistency in the code means that it can't
--   be processed. Examples include syntax errors (e.g. a missing {lit}`)`) and type
--   errors such as attempting to add a natural number to a function.

: 错误 (Errors)

  当代码中的不一致意味着无法处理时，就会产生错误。例如语法错误（例如缺少 {lit}`)`）和类型错误（例如试图将自然数加到函数上）。

-- : Warnings

--   Warnings describe potential problems with the code, such as the presence of {lean}`sorry`.
--   Unlike with errors, the code is not meaningless; however, warnings deserve careful attention.

: 警告 (Warnings)

  警告描述了代码的潜在问题，例如存在 {lean}`sorry`。与错误不同，代码并非毫无意义；但是，警告值得仔细关注。

-- : Information

--   Information doesn't indicate any problem with the code, and includes output from commands such as {kw}`#check` and {kw}`#eval`.

: 信息 (Information)

  信息并不表示代码有任何问题，包括 {kw}`#check` 和 {kw}`#eval` 等命令的输出。

-- Lean can check that a command produces the expected messages. If the messages match,
-- then any errors are disregarded; this can be used to ensure that the right errors occur.
-- If they don't, an error is produced. You can use the {kw}`#guard_msgs` command to indicate
-- which messages are expected.

Lean 可以检查命令是否产生预期的消息。如果消息匹配，则忽略任何错误；这可用于确保发生正确的错误。
如果不匹配，则会产生错误。你可以使用 {kw}`#guard_msgs` 命令来指示预期的消息。

-- Here is an example:

这是一个例子：
```lean
/--
error: Type mismatch
  "Not a number"
has type
  String
but is expected to have type
  Nat
-/
#guard_msgs in
def x : Nat := "Not a number"
```

:::leanFirst
-- Including a message category in parentheses after {leanRef}`#guard_msgs` causes it to check only
-- the specified category, letting others through. In this example, {leanRef}`#eval` issues an error
-- due to the presence of {lean}`sorry`, but the warning that is always issued for {lean}`sorry` is displayed
-- as usual:

在 {leanRef}`#guard_msgs` 后的括号中包含消息类别会导致它仅检查指定的类别，而让其他类别通过。
在此示例中，{leanRef}`#eval` 由于存在 {lean}`sorry` 而发出错误，但通常针对 {lean}`sorry` 发出的警告照常显示：
```lean
/--
error: aborting evaluation since the expression depends on the
'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!'
command.
-/
#guard_msgs(error) in
#eval (sorry : Nat)
```
:::

-- Without the configuration, both messages are captured:

如果没有配置，则会捕获这两条消息：
```lean
/--
error: aborting evaluation since the expression depends on the
'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!'
command.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
#eval (sorry : Nat)
```

-- Some examples in this book use {leanRef}`#guard_msgs` to indicate expected errors.

本书中的一些示例使用 {leanRef}`#guard_msgs` 来指示预期的错误。

-- # Importing Files
# 导入文件
%%%
tag := "importing-files"
%%%

-- The goal of Lean's front end is to interpret user input, construct
-- formal expressions, and check that they are well-formed and type-correct.
-- Lean also supports the use of various editors, which provide
-- continuous checking and feedback. More information can be found on the
-- Lean [documentation pages](https://lean-lang.org/documentation/).

Lean 的前端的目标是解释用户的输入，构建形式化的表达式，并检查它们是否形式良好和类型正确。
Lean 还支持使用各种编辑器，这些编辑器提供持续的检查和反馈。更多信息可以在 Lean [文档](https://lean-lang.org/documentation/)上找到。

-- The definitions and theorems in Lean's standard library are spread
-- across multiple files. Users may also wish to make use of additional
-- libraries, or develop their own projects across multiple files. When
-- Lean starts, it automatically imports the contents of the library
-- {lit}`Init` folder, which includes a number of fundamental definitions
-- and constructions. As a result, most of the examples we present here
-- work “out of the box.”

Lean 的标准库中的定义和定理分布在多个文件中。用户也可能希望使用额外的库，或在多个文件中开发自己的项目。
当 Lean 启动时，它会自动导入库中 {lit}`Init` 文件夹的内容，其中包括一些基本定义和结构。
因此，我们在这里介绍的大多数例子都是“开箱即用”的。

-- If you want to use additional files, however, they need to be imported
-- manually, via an {kw}`import` statement at the beginning of a file. The
-- command

-- > {kw}`import`{lit}` Bar.Baz.Blah`


-- imports the file {lit}`Bar/Baz/Blah.olean`, where the descriptions are
-- interpreted relative to the Lean _search path_. Information as to how
-- the search path is determined can be found on the
-- [documentation pages](https://lean-lang.org/documentation/).
-- By default, it includes the standard library directory, and (in some contexts)
-- the root of the user's local project.

然而，如果你想使用其他文件，需要通过文件开头的 {kw}`import` 语句手动导入。命令

> {kw}`import`{lit}` Bar.Baz.Blah`

导入文件 {lit}`Bar/Baz/Blah.olean`，其中的描述是相对于 Lean _搜索路径_ 解释的。
关于如何确定搜索路径的信息可以在[文档](https://lean-lang.org/documentation/)中找到。
默认情况下，它包括标准库目录，以及（在某些情况下）用户的本地项目的根目录。

-- Importing is transitive. In other words, if you import {lit}`Foo` and {lit}`Foo` imports {lit}`Bar`,
-- then you also have access to the contents of {lit}`Bar`, and do not need to import it explicitly.

导入是传递性的。换句话说，如果你导入了 {lit}`Foo`，并且 {lit}`Foo` 导入了 {lit}`Bar`，
那么你也可以访问 {lit}`Bar` 的内容，而不需要明确导入它。

-- # More on Sections
# 小节（续）
%%%
tag := "more-on-sections"
%%%

-- Lean provides various sectioning mechanisms to help structure a
-- theory. You saw in {ref "variables-and-sections"}[Variables and Sections] that the
-- {kw}`section` command makes it possible not only to group together
-- elements of a theory that go together, but also to declare variables
-- that are inserted as arguments to theorems and definitions, as
-- necessary. Remember that the point of the {kw}`variable` command is to
-- declare variables for use in theorems, as in the following example:

Lean 提供了各种分段机制来帮助构造理论。你在 {ref "variables-and-sections"}[变量和小节] 中看到，
{kw}`section` 命令不仅可以将理论中的元素组合在一起，还可以在必要时声明变量，作为定理和定义的参数插入。
请记住，{kw}`variable` 命令的意义在于声明变量，以便在定理中使用，如下面的例子：

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

-- The definition of {leanRef}`double` does not have to declare {leanRef}`x` as an
-- argument; Lean detects the dependence and inserts it
-- automatically. Similarly, Lean detects the occurrence of {leanRef}`x` in
-- {leanRef}`t1` and {leanRef}`t2`, and inserts it automatically there, too.
-- Note that {leanRef}`double` does _not_ have {leanRef}`y` as argument. Variables are only
-- included in declarations where they are actually used.

{leanRef}`double` 的定义不需要声明 {leanRef}`x` 作为参数；Lean 检测到这种依赖关系并自动插入。
同样，Lean 检测到 {leanRef}`x` 在 {leanRef}`t1` 和 {leanRef}`t2` 中的出现，也会自动插入。
注意，{leanRef}`double` _没有_ {leanRef}`y` 作为参数。变量只包括在实际使用的声明中。

-- # More on Namespaces
# 命名空间（续）
%%%
tag := "more-on-namespaces"
%%%

-- In Lean, identifiers are given by hierarchical _names_ like
-- {lit}`Foo.Bar.baz`. We saw in {ref "namespaces"}[Namespaces] that Lean provides
-- mechanisms for working with hierarchical names. The command
-- {kw}`namespace`{lit}` Foo` causes {lit}`Foo` to be prepended to the name of each
-- definition and theorem until {kw}`end`{lit}` Foo` is encountered. The command
-- {kw}`open`{lit}` Foo` then creates temporary _aliases_ to definitions and
-- theorems that begin with prefix {lit}`Foo`.

在 Lean 中，标识符是由层次化的 _名称_ 给出的，如 {lit}`Foo.Bar.baz`。
我们在 {ref "namespaces"}[命名空间] 一节中看到，Lean 提供了处理分层名称的机制。
命令 {kw}`namespace`{lit}` Foo` 导致 {lit}`Foo` 被添加到每个定义和定理的名称中，直到遇到 {kw}`end`{lit}` Foo`。
命令 {kw}`open`{lit}` Foo` 然后为以 {lit}`Foo` 开头的定义和定理创建临时的 _别名_ 。

```lean
namespace Foo
def bar : Nat := 1
end Foo

open Foo

#check bar

#check Foo.bar
```

-- The following definition

下面的定义

```lean
def Foo.bar : Nat := 1
```

-- is treated as a macro, and expands to

被看成一个宏，展开成

```lean
namespace Foo
def bar : Nat := 1
end Foo
```

-- Although the names of theorems and definitions have to be unique, the
-- aliases that identify them do not. When we open a namespace, an
-- identifier may be ambiguous. Lean tries to use type information to
-- disambiguate the meaning in context, but you can always disambiguate
-- by giving the full name. To that end, the string {lit}`_root_` is an
-- explicit description of the empty prefix.

尽管定理和定义的名称必须是唯一的，但标识它们的别名却不是。当我们打开一个命名空间时，一个标识符可能是模糊的。
Lean 试图使用类型信息来消除上下文中的含义，但你总是可以通过给出全名来消除歧义。
为此，字符串 {lit}`_root_` 是对空前缀的明确表述。

```lean
def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String

-- This reference is ambiguous:
-- #check add

#check String.add           -- String.add (a b : String) : String

#check Bool.add             -- Bool.add (a b : Bool) : Bool

#check _root_.add           -- _root_.add (α β : Type) : Type

#check add "hello" "world"  -- "hello".add "world" : String

#check add true false       -- true.add false : Bool

#check add Nat Nat          -- _root_.add Nat Nat : Type
```

-- We can prevent the shorter alias from being created by using the {kw}`protected` keyword:

我们可以通过使用 {kw}`protected` 关键字来阻止创建较短的别名：

```lean
protected def Foo.bar : Nat := 1

open Foo

/-- error: Unknown identifier `bar` -/
#guard_msgs in
#check bar -- error

#check Foo.bar
```

-- This is often used for names like {name}`Nat.rec` and {name}`Nat.recOn`, to prevent
-- overloading of common names.

-- The {leanRef}`open` command admits variations. The command

这通常用于像 {name}`Nat.rec` 和 {name}`Nat.recOn` 这样的名称，以防止普通名称的重载。

{leanRef}`open` 命令允许变体。命令

```lean
open Nat (succ zero gcd)

#check zero     -- Nat.zero : Nat

#eval gcd 15 6  -- 3
```

-- creates aliases for only the identifiers listed. The command

仅对列出的标识符创建了别名。命令

```lean
open Nat hiding succ gcd

#check zero     -- Nat.zero : Nat

/-- error: Unknown identifier `gcd` -/
#guard_msgs in
#eval gcd 15 6  -- error

#eval Nat.gcd 15 6  -- 3
```

-- creates aliases for everything in the {lit}`Nat` namespace _except_ the identifiers listed.

给 {lit}`Nat` 命名空间中 _除了_ 被列出的标识符都创建了别名。

```lean
open Nat renaming mul → times, add → plus

#eval plus (times 2 2) 3  -- 7
```

-- creates aliases renaming {lean}`Nat.mul` to {leanRef}`times` and {lean}`Nat.add` to {leanRef}`plus`.

-- It is sometimes useful to {kw}`export` aliases from one namespace to another, or to the top level. The command

将 {lean}`Nat.mul` 更名为 {leanRef}`times`，{lean}`Nat.add` 更名为 {leanRef}`plus`。

有时，将别名从一个命名空间 {kw}`export` 到另一个命名空间，或者导出到顶层是很有用的。命令

```lean
export Nat (succ add sub)
```

-- creates aliases for {leanRef}`succ`, {leanRef}`add`, and {leanRef}`sub` in the current
-- namespace, so that whenever the namespace is open, these aliases are
-- available. If this command is used outside a namespace, the aliases
-- are exported to the top level.

在当前命名空间中为 {leanRef}`succ`、{leanRef}`add` 和 {leanRef}`sub` 创建别名，
这样无论何时命名空间被打开，这些别名都可以使用。如果这个命令在名字空间之外使用，那么这些别名会被输出到顶层。

-- # Attributes
# 属性
%%%
tag := "attributes"
%%%

-- The main function of Lean is to translate user input to formal
-- expressions that are checked by the kernel for correctness and then
-- stored in the environment for later use. But some commands have other
-- effects on the environment, either assigning attributes to objects in
-- the environment, defining notation, or declaring instances of type
-- classes, as described in the chapter on {ref "type-classes"}[type classes]. Most of
-- these commands have global effects, which is to say, they remain
-- in effect not only in the current file, but also in any file that
-- imports it. However, such commands often support the {kw}`local` modifier,
-- which indicates that they only have effect until
-- the current {kw}`section` or {leanRef}`namespace` is closed, or until the end
-- of the current file.

Lean 的主要功能是把用户的输入翻译成形式化的表达式，由内核检查其正确性，然后存储在环境中供以后使用。
但是有些命令对环境有其他的影响，或者给环境中的对象分配属性，定义符号，或者声明类型类的实例，
如 {ref "type-classes"}[类型类] 一章所述。这些命令大多具有全局效应，也就是说，它们不仅在当前文件中保持有效，
而且在任何导入它的文件中也保持有效。然而，这类命令通常支持 {kw}`local` 修饰符，
这表明它们只在当前 {kw}`section` 或 {leanRef}`namespace` 关闭前或当前文件结束前有效。

-- In {ref "using-the-simplifier"}[Using the Simplifier],
-- we saw that theorems can be annotated with the {attr}`[simp]` attribute,
-- which makes them available for use by the simplifier.
-- The following example defines the prefix relation on lists,
-- proves that this relation is reflexive, and assigns the {attr}`[simp]` attribute to that theorem.

在 {ref "using-the-simplifier"}[使用简化器] 一节中，我们看到可以用 {attr}`[simp]` 属性来注释定理，
这使它们可以被简化器使用。下面的例子定义了列表的前缀关系，证明了这种关系是自反的，并为该定理分配了 {attr}`[simp]` 属性。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

-- The simplifier then proves {leanRef}`isPrefix [1, 2, 3] [1, 2, 3]` by rewriting it to {lean}`True`.

-- One can also assign the attribute any time after the definition takes place:

然后简化器通过将其改写为 {lean}`True` 来证明 {leanRef}`isPrefix [1, 2, 3] [1, 2, 3]`。

你也可以在做出定义后的任何时候分配属性：

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
 ∃ t, l₁ ++ t = l₂
------
theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self
```

-- In all these cases, the attribute remains in effect in any file that
-- imports the one in which the declaration occurs. Adding the {kw}`local`
-- modifier restricts the scope:

在所有这些情况下，该属性在任何导入该声明的文件中仍然有效。添加 {kw}`local` 修饰符可以限制范围：

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
 ∃ t, l₁ ++ t = l₂
------
section

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

/-- error: `simp` made no progress -/
#guard_msgs in
example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp
```

:::leanFirst
-- For another example, we can use the {kw}`instance` command to assign the
-- notation {lit}`≤` to the {leanRef}`isPrefix` relation. That command, which will
-- be explained in the chapter on {ref "type-classes"}[type classes], works by
-- assigning an {attr}`[instance]` attribute to the associated definition.

另一个例子，我们可以使用 {kw}`instance` 命令来给 {leanRef}`isPrefix` 关系分配符号 {lit}`≤`。
该命令将在 {ref "type-classes"}[类型类] 一章中解释，它的工作原理是给相关定义分配一个 {attr}`[instance]` 属性。

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

instance : LE (List α) where
  le := isPrefix

theorem List.isPrefix_self (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

:::

-- That assignment can also be made local:

这个分配也可以是局部的：

```lean
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂
------
def instLe : LE (List α) :=
  { le := isPrefix }

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

/--
error: failed to synthesize
  LE (List α)

Hint: Additional diagnostic information may be available using the
`set_option diagnostics true` command.
-/
#guard_msgs in
example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
```

-- In {ref "notation"}[Notation] below, we will discuss Lean's
-- mechanisms for defining notation, and see that they also support the
-- {kw}`local` modifier. However, in {ref "setting-options"}[Setting Options], we will
-- discuss Lean's mechanisms for setting options, which does _not_ follow
-- this pattern: options can _only_ be set locally, which is to say,
-- their scope is always restricted to the current section or current
-- file.

在下面的 {ref "notation"}[符号] 一节中，我们将讨论 Lean 定义符号的机制，并看到它们也支持 {kw}`local` 修饰符。
然而，在 {ref "setting-options"}[设置选项] 一节中，我们将讨论 Lean 设置选项的机制，它并 _不_ 遵循这种模式：
选项 _只能_ 在局部设置，也就是说，它们的范围总是限制在当前小节或当前文件中。

-- # More on Implicit Arguments
# 隐参数（续）
%%%
tag := "more-on-implicit-arguments"
%%%

:::setup

```
variable (α : Type u) (β : α → Type v) (t : {x : α} → β x)
```


-- In {ref "implicit-arguments"}[Implicit Arguments],
-- we saw that if Lean displays the type
-- of a term {lean}`t` as {lean}`{x : α} → β x`, then the curly brackets
-- indicate that {leanRef}`x` has been marked as an _implicit argument_ to
-- {lean}`t`. This means that whenever you write {lean}`t`, a placeholder, or
-- “hole,” is inserted, so that {lean}`t` is replaced by {lean}`@t _`. If you
-- don't want that to happen, you have to write {lean}`@t` instead.

在 {ref "implicit-arguments"}[隐参数] 一节中，我们看到，如果 Lean 将术语 {lean}`t` 的类型显示为 {lean}`{x : α} → β x`，
那么大括号表示 {leanRef}`x` 被标记为 {lean}`t` 的 _隐参数_。这意味着每当你写 {lean}`t` 时，就会插入一个占位符，
或者说“洞”，这样 {lean}`t` 就会被 {lean}`@t _` 取代。如果你不希望这种情况发生，你必须写 {lean}`@t` 来代替。
:::


:::setup
```
def f (x : Nat) {y : Nat} (z : Nat) : Nat := x + y + z
-- Equivalent:
example := f 7
example := @f 7 _
```

-- Notice that implicit arguments are inserted eagerly. Suppose we define
-- a function {lean}`f : (x : Nat) → {y : Nat} → (z : Nat) → Nat`.
-- Then, when we write the expression {lean}`f 7` without further
-- arguments, it is parsed as {lean}`@f 7 _`.

请注意，隐参数是急于插入的。假设我们定义一个函数 {lean}`f : (x : Nat) → {y : Nat} → (z : Nat) → Nat`。
那么，当我们写表达式 {lean}`f 7` 时，没有进一步的参数，它会被解析为 {lean}`@f 7 _`。
:::

:::setup
```
def f (x : Nat) {{y : Nat}} (z : Nat) : Nat := x + y + z
-- Just f 7
example := f 7
-- These are equivalent:
example := @f 7 _ 3
example := f 7 3
-- Alternative syntax:
def f' (x : Nat) ⦃y : Nat⦄ (z : Nat) : Nat := x + y + z
```

-- Lean offers a weaker annotation which specifies that a placeholder should only be added
-- _before_ a subsequent explicit argument. It can be written with double braces, so the type of {lean}`f` would be
-- {lean}`f : (x : Nat) → {{y : Nat}} → (z : Nat) → Nat`.
-- With this annotation, the expression {lean}`f 7` would be parsed as is, whereas {lean}`f 7 3` would be
-- parsed as {lean}`@f 7 _ 3`, just as it would be with the strong annotation.
-- This annotation can also be written as {lit}`⦃y : Nat⦄`, where the Unicode brackets are entered
-- as {kbd}`\{{` and {kbd}`\}}`, respectively.

Lean 提供了一个较弱的注释，它指定了一个占位符只应在后一个显式参数 _之前_ 添加。
这个注释可以用双大括号写，所以 {lean}`f` 的类型是 {lean}`f : (x : Nat) → {{y : Nat}} → (z : Nat) → Nat`。
有了这个注释，表达式 {lean}`f 7` 将被解析为原样，而 {lean}`f 7 3` 将被解析为 {lean}`@f 7 _ 3`，就像使用强注释一样。
这个注释也可以写成 {lit}`⦃y : Nat⦄`，其中的 Unicode 括号输入方式为 {kbd}`\{{` 和 {kbd}`\}}`。
:::


-- To illustrate the difference, consider the following example, which
-- shows that a reflexive euclidean relation is both symmetric and
-- transitive.

为了说明这种区别，请看下面的例子，它表明一个自反的欧几里得关系既是对称的又是传递的。

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def Euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : Euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : transitive r :=
 th2 (th1 reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : Euclidean r)

#check euclr
```

-- The results are broken down into small steps: {leanRef}`th1` shows that a
-- relation that is reflexive and euclidean is symmetric, and {leanRef}`th2`
-- shows that a relation that is symmetric and euclidean is
-- transitive. Then {leanRef}`th3` combines the two results. But notice that we
-- have to manually disable the implicit arguments in {leanRef}`euclr`, because
-- otherwise too many implicit arguments are inserted. The problem goes
-- away if we use weak implicit arguments:

这些结果被分解成几个小步骤：{leanRef}`th1` 表明自反和欧氏的关系是对称的，{leanRef}`th2` 表明对称和欧氏的关系是传递的。
然后 {leanRef}`th3` 结合这两个结果。但是请注意，我们必须手动禁用 {leanRef}`euclr` 中的隐参数，
否则会插入太多的隐参数。如果我们使用弱隐式参数，这个问题就会消失：

```lean
def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b : α}}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r b c → r a c

def Euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : Euclidean r)
            : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : transitive r :=
  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop)
variable (euclr : Euclidean r)

#check euclr  -- euclr : Euclidean r
```

-- There is a third kind of implicit argument that is denoted with square
-- brackets, {lit}`[` and {lit}`]`. These are used for type classes, as
-- explained in the chapter on {ref "type-classes"}[type classes].

还有第三种隐式参数，用方括号表示，{lit}`[` 和 {lit}`]`。这些是用于类型类的，在 {ref "type-classes"}[类型类] 一章中解释。

-- # Notation
# 符号
%%%
tag := "notation"
%%%

-- Identifiers in Lean can include any alphanumeric characters, including
-- Greek characters (other than ∀ , Σ , and λ , which, as we have seen,
-- have a special meaning in the dependent type theory). They can also
-- include subscripts, which can be entered by typing {kbd}`\_` followed by
-- the desired subscripted character.

Lean 中的标识符可以包含任何字母数字字符，包括希腊字符（除了 ∀、Σ 和 λ，正如我们所见，它们在依值类型论中具有特殊含义）。
它们还可以包含下标，可以通过键入 {kbd}`\_` 后跟所需的下标字符来输入。

-- Lean's parser is extensible, which is to say, we can define new notation.

Lean 的解析器是可扩展的，也就是说，我们可以定义新的符号。

-- Lean's syntax can be extended and customized by users at every level,
-- ranging from basic “mixfix” notations to custom elaborators.  In fact,
-- all builtin syntax is parsed and processed using the same mechanisms
-- and APIs open to users.  In this section, we will describe and explain
-- the various extension points.

Lean 的语法可以由用户在各个层面上进行扩展和自定义，从基本的“混合（mixfix）”符号到自定义阐述器。
事实上，所有内置语法都是使用向用户开放的相同机制和 API 进行解析和处理的。在本节中，我们将描述和解释各种扩展点。

-- While introducing new notations is a relatively rare feature in
-- programming languages and sometimes even frowned upon because of its
-- potential to obscure code, it is an invaluable tool in formalization
-- for expressing established conventions and notations of the respective
-- field succinctly in code.  Going beyond basic notations, Lean's
-- ability to factor out common boilerplate code into (well-behaved)
-- macros and to embed entire custom domain specific languages (DSLs) to
-- textually encode subproblems efficiently and readably can be of great
-- benefit to both programmers and proof engineers alike.

虽然引入新符号在编程语言中是一个相对罕见的功能，有时甚至因为可能使代码变得晦涩难懂而不被看好，
但在形式化中，它是一个无价的工具，可以简洁地在代码中表达相关领域既定的约定和符号。
除了基本符号之外，Lean 能够将常见的样板代码分解为（行为良好的）宏，并嵌入整个自定义领域特定语言（DSL），
以高效且可读地对子问题进行文本编码，这对程序员和证明工程师都大有裨益。

-- ## Notations and Precedence
## 符号和优先级
%%%
tag := "notations-and-precedence"
%%%

-- The most basic syntax extension commands allow introducing new (or
-- overloading existing) prefix, infix, and postfix operators.

最基本的语法扩展命令允许引入新的（或重载现有的）前缀、中缀和后缀运算符。

```lean
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
postfix:max "⁻¹"  => Inv.inv
```

-- After the initial command name describing the operator kind (its
-- “{deftech}[fixity]”), we give the _parsing precedence_ of the operator preceded
-- by a colon {lit}`:`, then a new or existing token surrounded by double
-- quotes (the whitespace is used for pretty printing), then the function
-- this operator should be translated to after the arrow {lit}`=>`.

在描述运算符种类（其“{deftech}[固定性]”）的初始命令名称之后，我们给出运算符的 _解析优先级_，
前面加冒号 {lit}`:`，然后是用双引号括起来的新标记或现有标记（空格用于漂亮打印），
然后是箭头 {lit}`=>` 之后该运算符应转换为的函数。

-- The precedence is a natural number describing how “tightly” an
-- operator binds to its arguments, encoding the order of operations.  We
-- can make this more precise by looking at the commands the above unfold to:

优先级是一个自然数，描述运算符与其参数绑定的“紧密”程度，编码运算顺序。
我们可以通过查看上面展开的命令来更精确地说明这一点：

```lean
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
 -- `max` is a shorthand for precedence 1024:
notation:1024 arg:1024 "⁻¹" => Inv.inv arg
```

:::setup
```
variable {p : Nat} {a b c : α} [Add α] [Pow α α]
```
-- It turns out that all commands from the first code block are in fact
-- command _macros_ translating to the more general {leanRef}`notation` command.
-- We will learn about writing such macros below.  Instead of a single
-- token, the {leanRef}`notation` command accepts a mixed sequence of tokens and
-- named term placeholders with precedences, which can be referenced on
-- the right-hand side of {lit}`=>` and will be replaced by the respective
-- term parsed at that position. A placeholder with precedence {lean}`p`
-- accepts only notations with precedence at least {lean}`p` in that place.
-- Thus the string {lean}`a + b + c` cannot be parsed as the equivalent of
-- {lean}`a + (b + c)` because the right-hand side operand of an {leanRef}`infixl` notation
-- has precedence one greater than the notation itself.  In contrast,
-- {leanRef}`infixr` reuses the notation's precedence for the right-hand side
-- operand, so {lean}`a ^ b ^ c` _can_ be parsed as {lean}`a ^ (b ^ c)`.  Note that
-- if we used {leanRef}`notation` directly to introduce an infix notation like

事实证明，第一个代码块中的所有命令实际上都是命令 _宏_，它们转换为更通用的 {leanRef}`notation` 命令。
我们将在下面学习编写此类宏。{leanRef}`notation` 命令不接受单个标记，而是接受标记和具有优先级的命名项占位符的混合序列，
这些占位符可以在 {lit}`=>` 的右侧引用，并将被在该位置解析的相应项替换。优先级为 {lean}`p` 的占位符在该位置仅接受优先级至少为 {lean}`p` 的符号。
因此，字符串 {lean}`a + b + c` 不能解析为等同于 {lean}`a + (b + c)`，因为 {leanRef}`infixl` 符号的右侧操作数的优先级比符号本身大 1。
相比之下，{leanRef}`infixr` 对右侧操作数重用符号的优先级，因此 {lean}`a ^ b ^ c` _可以_ 解析为 {lean}`a ^ (b ^ c)`。
请注意，如果我们直接使用 {leanRef}`notation` 引入中缀符号，例如
:::

```lean
def wobble : α → β → γ := sorry
------
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs
```

:::setup
```
variable (a : α) (b : β) (c : γ)
def wobble : α → β → γ := sorry
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs

```

-- where the precedences do not sufficiently determine associativity,
-- Lean's parser will default to right associativity.  More precisely,
-- Lean's parser follows a local _longest parse_ rule in the presence of
-- ambiguous grammars: when parsing the right-hand side of {lit}`a ~` in
-- {lean}`a ~ b ~ c`, it will continue parsing as long as possible (as the current
-- precedence allows), not stopping after {leanRef}`b` but parsing {leanRef}`~ c` as well.
-- Thus the term is equivalent to {lean}`a ~ (b ~ c)`.

其中优先级不足以确定结合性，Lean 的解析器将默认为右结合。更准确地说，
在存在歧义语法的情况下，Lean 的解析器遵循局部 _最长解析_ 规则：当解析 {lean}`a ~ b ~ c` 中的 {lit}`a ~` 的右侧时，
它将尽可能长时间地继续解析（只要当前优先级允许），不会在 {leanRef}`b` 之后停止，而是也会解析 {leanRef}`~ c`。
因此，该项等同于 {lean}`a ~ (b ~ c)`。
:::

-- As mentioned above, the {leanRef}`notation` command allows us to define
-- arbitrary _mixfix_ syntax freely mixing tokens and placeholders.

如上所述，{leanRef}`notation` 命令允许我们定义任意 _混合_ 语法，自由混合标记和占位符。

```lean
set_option quotPrecheck false
------
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ
```

-- Placeholders without precedence default to {lit}`0`, i.e. they accept notations of any precedence in their place.
-- If two notations overlap, we again apply the longest parse rule:

没有优先级的占位符默认为 {lit}`0`，即它们在其位置接受任何优先级的符号。
如果两个符号重叠，我们再次应用最长解析规则：

```lean
notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
```

-- The new notation is preferred to the binary notation since the latter,
-- before chaining, would stop parsing after {leanRef}`1 + 2`.  If there are
-- multiple notations accepting the same longest parse, the choice will
-- be delayed until elaboration, which will fail unless exactly one
-- overload is type-correct.

新符号优于二元符号，因为后者在链接之前会在 {leanRef}`1 + 2` 之后停止解析。
如果有多个符号接受相同的最长解析，则选择将推迟到阐述阶段，除非恰好有一个重载是类型正确的，否则阐述将失败。

-- # Coercions
# 强制转换
%%%
tag := "coercions"
%%%

-- In Lean, the type of natural numbers, {lean}`Nat`, is different from the
-- type of integers, {lean}`Int`. But there is a function {lean}`Int.ofNat` that
-- embeds the natural numbers in the integers, meaning that we can view
-- any natural number as an integer, when needed. Lean has mechanisms to
-- detect and insert _coercions_ of this sort. Coercions can be explicitly
-- requested using the overloaded {lit}`↑` operator.

在 Lean 中，自然数的类型 {lean}`Nat`，与整数的类型 {lean}`Int` 不同。
但是有一个函数 {lean}`Int.ofNat` 将自然数嵌入整数中，这意味着我们可以在需要时将任何自然数视为整数。
Lean 有机制来检测和插入这种 _强制转换_。可以使用重载的 {lit}`↑` 运算符显式请求强制转换。

```lean
variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + ↑m : Int

#check i + m + j  -- i + ↑m + j : Int

#check i + m + n  -- i + ↑m + ↑n : Int
```

-- # Displaying Information
# 显示信息
%%%
tag := "displaying-information"
%%%

-- There are a number of ways in which you can query Lean for information
-- about its current state and the objects and theorems that are
-- available in the current context. You have already seen two of the
-- most common ones, {kw}`#check` and {kw}`#eval`. Remember that {kw}`#check`
-- is often used in conjunction with the {lit}`@` operator, which makes all
-- of the arguments to a theorem or definition explicit. In addition, you
-- can use the {kw}`#print` command to get information about any
-- identifier. If the identifier denotes a definition or theorem, Lean
-- prints the type of the symbol, and its definition. If it is a constant
-- or an axiom, Lean indicates that fact, and shows the type.

有很多方法可以让你查询 Lean 的当前状态以及当前上下文中可用的对象和定理的信息。
你已经看到了两个最常见的方法，{kw}`#check` 和 {kw}`#eval`。
请记住，{kw}`#check` 经常与 {lit}`@` 运算符一起使用，它使定理或定义的所有参数显式化。
此外，你可以使用 {kw}`#print` 命令来获得任何标识符的信息。
如果标识符表示一个定义或定理，Lean 会打印出符号的类型，以及它的定义。
如果它是一个常数或公理，Lean 会指出它并显示其类型。

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

-- # Setting Options
# 设置选项
%%%
tag := "setting-options"
%%%

-- Lean maintains a number of internal variables that can be set by users
-- to control its behavior. The syntax for doing so is as follows:

Lean 维护着一些内部变量，用户可以通过设置这些变量来控制其行为。语法如下：


{kw}`set_option`{lit}` <name> <value>`


-- One very useful family of options controls the way Lean's _pretty printer_ displays terms. The following options take an input of true or false:

有一系列非常有用的选项可以控制 Lean 的 _美观打印（pretty printer）_ 显示项的方式。下列选项的输入值为 true 或 false：

```
pp.explicit  : display implicit arguments
pp.universes : display hidden universe parameters
pp.notation  : display output using defined notations
```

-- As an example, the following settings yield much longer output:

例如，以下设置会产生更长的输出：

```lean
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false

#check 2 + 2 = 4

#reduce (fun x => x + 2) = (fun x => x + 3)

#check (fun x => x + 1) 1
```

-- The command {leanCommand}`set_option pp.all true` carries out these settings all
-- at once, whereas {leanCommand}`set_option pp.all false` reverts to the previous
-- values. Pretty printing additional information is often very useful
-- when you are debugging a proof, or trying to understand a cryptic
-- error message. Too much information can be overwhelming, though, and
-- Lean's defaults are generally sufficient for ordinary interactions.

命令 {leanCommand}`set_option pp.all true` 一次性执行这些设置，
而 {leanCommand}`set_option pp.all false` 则恢复到之前的值。
当你调试一个证明，或试图理解一个神秘的错误信息时，美观打印额外的信息往往是非常有用的。
不过太多的信息可能会让人不知所措，Lean 的默认值一般来说对普通的交互是足够的。

:::comment
```
<!--
# Elaboration Hints

When you ask Lean to process an expression like `λ x y z, f (x + y) z`, you are leaving information implicit. For example, the types of `x`, `y`, and `z` have to be inferred from the context, the notation `+` may be overloaded, and there may be implicit arguments to `f` that need to be filled in as well. Moreover, we will see in :numref:`Chapter %s <type_classes>` that some implicit arguments are synthesized by a process known as _type class resolution_. And we have also already seen in the last chapter that some parts of an expression can be constructed by the tactic framework.

Inferring some implicit arguments is straightforward. For example, suppose a function `f` has type `Π {α : Type*}, α → α → α` and Lean is trying to parse the expression `f n`, where `n` can be inferred to have type `nat`. Then it is clear that the implicit argument `α` has to be `nat`. However, some inference problems are _higher order_. For example, the substitution operation for equality, `eq.subst`, has the following type:

.. code-block:: text

    eq.subst : ∀ {α : Sort u} {p : α → Prop} {a b : α},
                 a = b → p a → p b

Now suppose we are given `a b : ℕ` and `h₁ : a = b` and `h₂ : a * b > a`. Then, in the expression `eq.subst h₁ h₂`, `P` could be any of the following:

-  `λ x, x * b > x`
-  `λ x, x * b > a`
-  `λ x, a * b > x`
-  `λ x, a * b > a`

In other words, our intent may be to replace either the first or second `a` in `h₂`, or both, or neither. Similar ambiguities arise in inferring induction predicates, or inferring function arguments. Even second-order unification is known to be undecidable. Lean therefore relies on heuristics to fill in such arguments, and when it fails to guess the right ones, they need to be provided explicitly.

To make matters worse, sometimes definitions need to be unfolded, and sometimes expressions need to be reduced according to the computational rules of the underlying logical framework. Once again, Lean has to rely on heuristics to determine what to unfold or reduce, and when.

There are attributes, however, that can be used to provide hints to the elaborator. One class of attributes determines how eagerly definitions are unfolded: constants can be marked with the attribute `[reducible]`, `[semireducible]`, or `[irreducible]`. Definitions are marked `[semireducible]` by default. A definition with the `[reducible]` attribute is unfolded eagerly; if you think of a definition as serving as an abbreviation, this attribute would be appropriate. The elaborator avoids unfolding definitions with the `[irreducible]` attribute. Theorems are marked `[irreducible]` by default, because typically proofs are not relevant to the elaboration process.

It is worth emphasizing that these attributes are only hints to the elaborator. When checking an elaborated term for correctness, Lean's kernel will unfold whatever definitions it needs to unfold. As with other attributes, the ones above can be assigned with the `local` modifier, so that they are in effect only in the current section or file.

Lean also has a family of attributes that control the elaboration strategy. A definition or theorem can be marked `[elab_with_expected_type]`, `[elab_simple]`. or `[elab_as_eliminator]`. When applied to a definition `f`, these bear on elaboration of an expression `f a b c ...` in which `f` is applied to arguments. With the default attribute, `[elab_with_expected_type]`, the arguments `a`, `b`, `c`, ... are elaborating using information about their expected type, inferred from `f` and the previous arguments. In contrast, with `[elab_simple]`, the arguments are elaborated from left to right without propagating information about their types. The last attribute, `[elab_as_eliminator]`, is commonly used for eliminators like recursors, induction principles, and `eq.subst`. It uses a separate heuristic to infer higher-order parameters. We will consider such operations in more detail in the next chapter.

Once again, these attributes can be assigned and reassigned after an object is defined, and you can use the `local` modifier to limit their scope. Moreover, using the `@` symbol in front of an identifier in an expression instructs the elaborator to use the `[elab_simple]` strategy; the idea is that, when you provide the tricky parameters explicitly, you want the elaborator to weigh that information heavily. In fact, Lean offers an alternative annotation, `@@`, which leaves parameters before the first higher-order parameter implicit. For example, `@@eq.subst` leaves the type of the equation implicit, but makes the context of the substitution explicit.

-->
```
:::

-- # Using the Library
# 使用库
%%%
tag := "using-the-library"
%%%

-- To use Lean effectively you will inevitably need to make use of
-- definitions and theorems in the library. Recall that the {kw}`import`
-- command at the beginning of a file imports previously compiled results
-- from other files, and that importing is transitive; if you import
-- {lit}`Foo` and {lit}`Foo` imports {lit}`Bar`, then the definitions and theorems
-- from {lit}`Bar` are available to you as well. But the act of opening a
-- namespace, which provides shorter names, does not carry over. In each
-- file, you need to open the namespaces you wish to use.

为了有效地使用 Lean，你将不可避免地需要使用库中的定义和定理。
回想一下，文件开头的 {kw}`import` 命令会从其他文件中导入之前编译的结果，而且导入是传递的；
如果你导入了 {lit}`Foo`，{lit}`Foo` 又导入了 {lit}`Bar`，那么 {lit}`Bar` 的定义和定理也可以被你利用。
但是打开一个命名空间的行为，提供了更短的名字，并没有延续下去。在每个文件中，你需要打开你想使用的命名空间。

-- In general, it is important for you to be familiar with the library
-- and its contents, so you know what theorems, definitions, notations,
-- and resources are available to you. Below we will see that Lean's
-- editor modes can also help you find things you need, but studying the
-- contents of the library directly is often unavoidable. Lean's standard
-- library can be found online, on GitHub:

一般来说，你必须熟悉库和它的内容，这样你就知道有哪些定理、定义、符号和资源可供你使用。
下面我们将看到 Lean 的编辑器模式也可以帮助你找到你需要的东西，但直接研究库的内容往往是不可避免的。
Lean 的标准库在 GitHub 上：

- [https://github.com/leanprover/lean4/tree/master/src/Init](https://github.com/leanprover/lean4/tree/master/src/Init)

- [https://github.com/leanprover/lean4/tree/master/src/Std](https://github.com/leanprover/lean4/tree/master/src/Std)


-- You can see the contents of these directories and files using GitHub's
-- browser interface. If you have installed Lean on your own computer,
-- you can find the library in the {lit}`lean` folder, and explore it with
-- your file manager. Comment headers at the top of each file provide
-- additional information.

你可以使用 GitHub 的浏览器界面查看这些目录和文件的内容。如果你在自己的电脑上安装了 Lean，
你可以在 {lit}`lean` 文件夹中找到这个库，用你的文件管理器探索它。每个文件顶部的注释标题提供了额外的信息。

-- Lean's library developers follow general naming guidelines to make it
-- easier to guess the name of a theorem you need, or to find it using
-- tab completion in editors with a Lean mode that supports this, which
-- is discussed in the next section. Identifiers are generally
-- {lit}`camelCase`, and types are {lit}`CamelCase`. For theorem names,
-- we rely on descriptive names where the different components are separated
-- by {lit}`_`s. Often the name of theorem simply describes the conclusion:

Lean 库的开发者遵循一般的命名准则，以便于猜测你所需要的定理的名称，
或者在支持 Lean 模式的编辑器中用 Tab 自动补全来找到它，这将在下一节讨论。
标识符一般是 {lit}`camelCase`，而类型是 {lit}`CamelCase`。
对于定理的名称，我们依靠描述性的名称，其中不同的组成部分用 {lit}`_` 分开。
通常情况下，定理的名称只是描述结论：

```lean
#check Nat.succ_ne_zero

#check Nat.zero_add

#check Nat.mul_one

#check Nat.le_of_succ_le_succ
```

:::setup
```
open Nat
```

-- Remember that identifiers in Lean can be organized into hierarchical
-- namespaces. For example, the theorem named {lean}`le_of_succ_le_succ` in the
-- namespace {lit}`Nat` has full name {lean}`Nat.le_of_succ_le_succ`, but the shorter
-- name is made available by the command {kw}`open`{lit}` Nat` (for names not marked as
-- {kw}`protected`). We will see in the chapters on {ref "inductive-types"}[inductive types]
-- and {ref "structures-and-records"}[structures and records]
-- that defining structures and inductive data types in Lean generates
-- associated operations, and these are stored in
-- a namespace with the same name as the type under definition. For
-- example, the product type comes with the following operations:

请记住，Lean 中的标识符可以组织成层次化的命名空间。
例如，命名空间 {lit}`Nat` 中名为 {lean}`le_of_succ_le_succ` 的定理的全名是 {lean}`Nat.le_of_succ_le_succ`，
但是通过命令 {kw}`open`{lit}` Nat` 可以使用更短的名称（对于未标记为 {kw}`protected` 的名称）。
我们将在 {ref "inductive-types"}[归纳类型] 和 {ref "structures-and-records"}[结构体和记录] 章节中看到，
在 Lean 中定义结构体和归纳数据类型会生成相关的操作，这些操作存储在与定义类型同名的命名空间中。
例如，乘积类型带有以下操作：
:::

```lean
#check @Prod.mk

#check @Prod.fst

#check @Prod.snd

#check @Prod.rec
```

-- The first is used to construct a pair, whereas the next two,
-- {leanRef}`Prod.fst` and {leanRef}`Prod.snd`, project the two elements. The last,
-- {leanRef}`Prod.rec`, provides another mechanism for defining functions on a
-- product in terms of a function on the two components. Names like
-- {leanRef}`Prod.rec` are _protected_, which means that one has to use the full
-- name even when the {lit}`Prod` namespace is open.

第一个用于构造对，而接下来的两个 {leanRef}`Prod.fst` 和 {leanRef}`Prod.snd` 投影这两个元素。
最后一个 {leanRef}`Prod.rec` 提供了另一种机制，用于根据两个分量上的函数定义乘积上的函数。
像 {leanRef}`Prod.rec` 这样的名称是 _受保护的（protected）_，这意味着即使打开了 {lit}`Prod` 命名空间，也必须使用全名。

-- With the propositions as types correspondence, logical connectives are
-- also instances of inductive types, and so we tend to use dot notation
-- for them as well:

根据命题即类型对应关系，逻辑连接词也是归纳类型的实例，因此我们也倾向于对它们使用点符号：

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

-- # Auto Bound Implicit Arguments
# 自动绑定隐式参数
%%%
tag := "auto-bound-implicit-arguments"
%%%

-- :::leanFirst
-- In the previous section, we have shown how implicit arguments make functions more convenient to use.
-- However, functions such as {leanRef}`compose` are still quite verbose to define. Note that the universe
-- polymorphic {leanRef}`compose` is even more verbose than the one previously defined.

:::leanFirst
在上一节中，我们展示了隐式参数如何使函数使用起来更方便。
然而，像 {leanRef}`compose` 这样的函数定义起来仍然相当冗长。
请注意，宇宙多态的 {leanRef}`compose` 甚至比之前定义的那个还要冗长。

```lean
universe u v w

def compose {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```
:::

-- :::leanFirst
-- You can avoid the {kw}`universe` command by providing the universe parameters when defining {leanRef}`compose`.

:::leanFirst
你可以通过在定义 {leanRef}`compose` 时提供宇宙参数来避免使用 {kw}`universe` 命令。

```lean
def compose.{u, v, w}
    {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```
:::

-- ::::leanFirst
-- Lean 4 supports a new feature called _auto bound implicit arguments_. It makes functions such as
-- {leanRef}`compose` much more convenient to write. When Lean processes the header of a declaration,
-- any unbound identifier is automatically added as an implicit argument. With this feature we can write {leanRef}`compose` as

::::leanFirst
Lean 4 支持一项名为 _自动绑定隐式参数_ 的新功能。它使得像 {leanRef}`compose` 这样的函数编写起来更加方便。
当 Lean 处理声明的头部时，任何未绑定的标识符都会自动添加为隐式参数。有了这个功能，我们可以将 {leanRef}`compose` 写为：

:::TODO

Update and check details

:::

```lean
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose -- @compose : {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
```

-- Note that Lean inferred a more general type using {lean}`Sort` instead of {leanRef}`Type`.
-- ::::

请注意，Lean 使用 {lean}`Sort` 而不是 {leanRef}`Type` 推断出了更通用的类型。
::::

-- Although we love this feature and use it extensively when implementing Lean,
-- we realize some users may feel uncomfortable with it. Thus, you can disable it using
-- the command {leanCommand}`set_option autoImplicit false`.

虽然我们喜欢这个功能并在实现 Lean 时广泛使用它，但我们意识到一些用户可能会对此感到不舒服。
因此，你可以使用命令 {leanCommand}`set_option autoImplicit false` 禁用它。

```lean
set_option autoImplicit false

/--
error: Unknown identifier `β`
---
error: Unknown identifier `γ`
---
error: Unknown identifier `α`
---
error: Unknown identifier `β`
---
error: Unknown identifier `α`
---
error: Unknown identifier `γ`
-/
#guard_msgs in
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
```

-- # Implicit Lambdas
# 隐式 Lambda
%%%
tag := "implicit-lambdas"
%%%

-- :::TODO
-- Update this text after archaeology
-- :::

:::TODO
Update this text after archaeology
:::

-- :::leanFirst
-- When the expected type of an expression is a function that is awaiting implicit
-- arguments, the elaborator automatically introduces the corresponding lambdas.
-- For example, {leanRef}`pure`'s type states that the first argument is an implicit type
-- {leanRef}`α`, but {leanRef}`ReaderT.pure`'s first argument is the reader monad's context type {leanRef}`ρ`.
-- It is automatically surrounded with a {kw}`fun`{lit}` {α} => ...`, which allows the elaborator to
-- correctly fill in the implicit arguments in the body.

:::leanFirst
当表达式的预期类型是等待隐式参数的函数时，阐述器会自动引入相应的 lambda。
例如，{leanRef}`pure` 的类型表明第一个参数是隐式类型 {leanRef}`α`，
但 {leanRef}`ReaderT.pure` 的第一个参数是 reader monad 的上下文类型 {leanRef}`ρ`。
它会自动被 {kw}`fun`{lit}` {α} => ...` 包围，这允许阐述器正确填充主体中的隐式参数。

```lean
variable (ρ : Type) (m : Type → Type) [Monad m]
------
instance : Monad (ReaderT ρ m) where
  pure := ReaderT.pure
  bind := ReaderT.bind
```
:::

-- Users can disable the implicit lambda feature by using {lit}`@` or writing
-- a lambda expression with {lit}`{}` or {lit}`[]` binder annotations.  Here are
-- few examples

用户可以通过使用 {lit}`@` 或编写带有 {lit}`{}` 或 {lit}`[]` 绑定器注释的 lambda 表达式来禁用隐式 lambda 功能。
这里有几个例子：

```lean
set_option linter.unusedVariables false
namespace Ex2
------
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- In this example, implicit lambda introduction has been disabled because
-- we use `@` before {kw}`fun`
-- 在此示例中，隐式 lambda 引入已被禁用，因为我们在 {kw}`fun` 之前使用了 `@`
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- In this example, implicit lambda introduction has been disabled
-- because we used the binder annotation `{...}`
-- 在此示例中，隐式 lambda 引入已被禁用，因为我们使用了绑定器注释 `{...}`
def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
------
end Ex2
```

-- # Sugar for Simple Functions
# 简单函数的语法糖
%%%
tag := "sugar-for-simple-functions"
%%%

-- Lean includes a notation for describing simple functions using anonymous
-- placeholders rather than {kw}`fun`. When {lit}`·` occurs as part of a term,
-- the nearest enclosing parentheses become a function with the {lit}`·` as its argument.
-- If the parentheses include multiple placeholders without other intervening parentheses,
-- then they are made into arguments from left to right. Here are a few examples:

Lean 包含一种使用匿名占位符而不是 {kw}`fun` 来描述简单函数的符号。
当 {lit}`·` 作为项的一部分出现时，最近的封闭括号将成为一个以 {lit}`·` 为参数的函数。
如果括号包含多个占位符而没有其他中间括号，则它们将从左到右成为参数。这里有几个例子：

```lean
namespace Ex3
------
#check (· + 1) -- fun x => x + 1 : Nat → Nat

#check (2 - ·) -- fun x => 2 - x : Nat → Nat

#eval [1, 2, 3, 4, 5].foldl (· * ·) 1 -- 120

def f (x y z : Nat) :=
  x + y + z

#check (f · 1 ·) -- fun x1 x2 => f x1 1 x2 : Nat → Nat → Nat

#eval [(1, 2), (3, 4), (5, 6)].map (·.1) -- [1, 3, 5]
------
end Ex3
```

-- Nested parentheses introduce new functions. In the following example, two different lambda expressions are created:

嵌套括号引入新函数。在下面的示例中，创建了两个不同的 lambda 表达式：

```lean
#check (Prod.mk · (· + 1)) -- fun x => (x, fun x => x + 1) : ?m.2 → ?m.2 × (Nat → Nat)
```

-- # Named Arguments
# 命名参数
%%%
tag := "named-arguments"
%%%

-- Named arguments enable you to specify an argument for a parameter by
-- matching the argument with its name rather than with its position in
-- the parameter list.  If you don't remember the order of the parameters
-- but know their names, you can send the arguments in any order. You may
-- also provide the value for an implicit parameter when Lean failed to
-- infer it. Named arguments also improve the readability of your code by
-- identifying what each argument represents.

命名参数允许你通过将参数与其名称匹配而不是与其在参数列表中的位置匹配来指定参数的实参。
如果你不记得参数的顺序但知道它们的名称，你可以以任何顺序发送参数。
当 Lean 无法推断隐式参数时，你也可以为其提供值。
命名参数还通过标识每个参数代表的内容来提高代码的可读性。

```lean
def sum (xs : List Nat) :=
  xs.foldl (init := 0) (·+·)

#eval sum [1, 2, 3, 4]
-- 10

example {a b : Nat} {p : Nat → Nat → Nat → Prop}
    (h₁ : p a b b) (h₂ : b = a) :
    p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
```

-- In the following examples, we illustrate the interaction between named
-- and default arguments.

在下面的示例中，我们说明了命名参数和默认参数之间的交互。

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

-- You can use {lit}`..` to provide missing explicit arguments as {lit}`_`.
-- This feature combined with named arguments is useful for writing patterns. Here is an example:

你可以使用 {lit}`..` 将缺失的显式参数作为 {lit}`_` 提供。
此功能与命名参数结合使用对于编写模式非常有用。这里有一个例子：

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

-- Ellipses are also useful when explicit arguments can be automatically
-- inferred by Lean, and we want to avoid a sequence of {lit}`_`s.

当 Lean 可以自动推断显式参数，并且我们希望避免一连串的 {lit}`_` 时，省略号也很有用。

```lean
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
```
