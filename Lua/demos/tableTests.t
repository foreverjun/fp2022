  $ ./demoInterp.exe <<-EOF
  > -- Bool to string
  > function b2s(b) if b then return "true" else return "false" end end
  > print("Table tests")
  > a = {}
  > print("Empty table create: " .. b2s(a == {}))
  > a = {1, 2, 3}
  > print("Filled table create: " .. b2s(a[1] == 1 and a[2] == 2 and a[3] == 3))
  > a = {[6] = 5, 2, 3, [0] = "s"}
  > print("Filled indexed table create: " .. b2s(a[1] == 2 and a[2] == 3 and a[0] == "s" and a[6] == 5))
  > a = {["a"] = 4, ["b"] = 9, ["huge_giant_name"] = 42}
  > print("String indexing like fields: " .. b2s(a["a"] == 4 and a.b == 9 and a.huge_giant_name == 42))
  > a = {a = 4, b = 9, huge_giant_name = 42}
  > print("Creating fields in table: " .. b2s(a["a"] == 4 and a.b == 9 and a.huge_giant_name == 42))
  > a = {{{{}, {2}}, {}}, {b = {3}}}
  > print("Inner tables: " .. b2s(a[1][1][2][1] == 2 and a[2].b == {3} and a[2].b[1] == 3))
  > EOF
  Table tests
  Empty table create: true
  Filled table create: true
  Filled indexed table create: true
  String indexing like fields: true
  Creating fields in table: true
  Inner tables: true
  $ ./demoInterp.exe <<-EOF
  > print("Assign error test")
  > t = {}
  > t[1] = 1
  > print("ok")
  > t[2][1] = 2
  > print("not ok")
  > EOF
  Assign error test
  ok
  Interpreter failed with message: Attempt to index non table
  $ ./demoInterp.exe <<-EOF
  > -- In lua and in the initial implementation these were Hash tables
  > print("Non-recursive table")
  > t = {}
  > t.a = t
  > t.a = t
  > t.a = t
  > print(t)
  Non-recursive table
  {"a": {"a": {"a": {}}}}
