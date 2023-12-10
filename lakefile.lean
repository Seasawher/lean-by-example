import Lake
open Lake DSL

package «NTL» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "e9bcfc6e583d0784ece32475ca6f450126ef286f"

@[default_target]
lean_lib «NTL» where
  -- add any library configuration options here

/-!
`import` 文を自動生成するスクリプト
`lake run import_all` で実行できる
<https://github.com/lurk-lab/yatima/tree/main> からコードの大部分を拝借した
-/
section ImportAll
  def package_name := "NTL"

  partial def getLeanFilePaths (fp : FilePath) (acc : Array FilePath := #[]) :
      IO $ Array FilePath := do
    if ← fp.isDir then
      (← fp.readDir).foldlM (fun acc dir => getLeanFilePaths dir.path acc) acc
    else return if fp.extension == some "lean" then acc.push fp else acc

  open Lean (RBTree)

  def getAllFiles : ScriptM $ List String := do
    let paths := (← getLeanFilePaths ⟨package_name⟩).map toString
    let paths : RBTree String compare := RBTree.ofList paths.toList -- ordering
    return paths.toList

  def getImportsString : ScriptM String := do
    let paths ← getAllFiles
    let imports := paths.map fun p =>
      "import " ++ ((p.splitOn ".").head!.replace "/" ".").replace "\\" "."
    return s!"{"\n".intercalate imports}\n"

  script import_all do
    IO.FS.writeFile ⟨s!"{package_name}.lean"⟩ (← getImportsString)
    return 0

  script import_all? do
    let importsFromUser ← IO.FS.readFile ⟨s!"{package_name}.lean"⟩
    let expectedImports ← getImportsString
    if importsFromUser != expectedImports then
      IO.eprintln s!"Invalid import list in '{package_name}.lean'"
      IO.eprintln "Try running 'lake run import_all'"
      return 1
    return 0

end ImportAll
