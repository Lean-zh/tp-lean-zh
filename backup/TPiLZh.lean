import VersoManual
import TPiLZh.Intro
-- import TPiLZh.DependentTypeTheory
-- import TPiLZh.PropositionsAndProofs
-- import TPiLZh.QuantifiersEquality
-- import TPiLZh.Tactics
-- import TPiLZh.InteractingWithLean
-- import TPiLZh.InductiveTypes
-- import TPiLZh.InductionAndRecursion
-- import TPiLZh.StructuresAndRecords
-- import TPiLZh.TypeClasses
-- import TPiLZh.Conv
-- import TPiLZh.AxiomsComputation

open Verso.Genre Manual
open Verso Code External

open Verso Doc Elab in
open Lean (quote) in
@[role_expander versionString]
def versionString : RoleExpander
  | #[], #[] => do
    let version ← IO.FS.readFile "../examples/lean-toolchain"
    let version := version.dropPrefix "leanprover/lean4:" |>.dropPrefix "v" |>.trimAscii |>.copy
    pure #[← ``(Verso.Doc.Inline.code $(quote version))]
  | _, _ => throwError "Unexpected arguments"


#doc (Manual) "Lean 4 定理证明" =>

%%%
authors := ["Jeremy Avigad", "Leonardo de Moura", "Soonho Kong", "Sebastian Ullrich"]
authorshipNote := some "with contributions from the Lean Community"
%%%

[Lean-zh 项目组](https://github.com/Lean-zh) 译

-- This version of the text assumes you’re using Lean 4 (specifically {versionString}[]). See the
-- [Quickstart section](https://lean-lang.org/documentation/setup/) of
-- the Lean documentation to install Lean. The first version of this book was
-- written for Lean 2, and the Lean 3 version is available
-- [here](https://leanprover.github.io/theorem_proving_in_lean/).

本书假定你使用 Lean 4 {versionString}[]。安装方式参见 [Lean 4 中文社区](https://www.leanprover.cn/)
中的 [安装指南](https://www.leanprover.cn/install/) 一节。原版指南在[这里](https://lean-lang.org/documentation/setup/)。
本书的第一版为 Lean 2 编写，Lean 3 版请访问 [此处](https://leanprover.github.io/theorem_proving_in_lean/)。


{include 1 TPiLZh.Intro}
-- {include 1 TPiLZh.DependentTypeTheory}

-- {include 1 TPiLZh.PropositionsAndProofs}

-- {include 1 TPiLZh.QuantifiersEquality}

-- {include 1 TPiLZh.Tactics}

-- {include 1 TPiLZh.InteractingWithLean}

-- {include 1 TPiLZh.InductiveTypes}

-- {include 1 TPiLZh.InductionAndRecursion}

-- {include 1 TPiLZh.StructuresAndRecords}

-- {include 1 TPiLZh.TypeClasses}

-- {include 1 TPiLZh.Conv}

-- {include 1 TPiLZh.AxiomsComputation}
