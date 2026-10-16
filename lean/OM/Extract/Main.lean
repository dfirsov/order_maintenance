import OM.Extract.Rust

/-- `lake exe extract [path]`: write the generated Rust module (default `../rust/src/gen.rs`). -/
def main (args : List String) : IO Unit := do
  let path := args.headD "../rust/src/gen.rs"
  IO.FS.writeFile path OM.Extract.crate
  IO.println s!"wrote {path} ({OM.Extract.crate.length} bytes)"
