(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Micro_Rust_Shallow_Embedding_Tests
  imports
    Micro_Rust_Shallow_Embedding
begin

section\<open>Parsing and Evaluation Tests for the Shallow Embedding\<close>

text\<open>Comprehensive test coverage for the Micro Rust shallow embedding.
This file contains tests organized by language feature category.\<close>

subsection\<open>Literals and Basic Values\<close>

subsubsection\<open>Numeric Literals\<close>

term\<open>\<lbrakk> 0 \<rbrakk>\<close>
term\<open>\<lbrakk> 1 \<rbrakk>\<close>
term\<open>\<lbrakk> 42 \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>255 :: 8 word\<rrangle> \<rbrakk>\<close>

subsubsection\<open>Boolean Literals\<close>

term\<open>\<lbrakk>
  \<epsilon>\<open>Bool_Type.true\<close>
\<rbrakk>\<close>

term\<open>\<lbrakk> True \<rbrakk>\<close>
term\<open>\<lbrakk> False \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>False\<rrangle> \<rbrakk>\<close>

subsubsection\<open>Unit Literal\<close>

context
  fixes f :: \<open>unit \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>unit \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
term \<open>\<lbrakk> () \<rbrakk>\<close>
term \<open>\<lbrakk> (); () \<rbrakk>\<close>
term \<open>\<lbrakk> (); (); \<rbrakk>\<close>
term \<open>\<lbrakk> return (); \<rbrakk>\<close>
term \<open>\<lbrakk> return; \<rbrakk>\<close>
term \<open>\<lbrakk> f(()) \<rbrakk>\<close>
term \<open>\<lbrakk> g((),True) \<rbrakk>\<close>
end

subsubsection\<open>String Literals\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
term \<open>\<lbrakk> panic!("oh no!") \<rbrakk>\<close>
term \<open>\<lbrakk> panic!( \<llangle>''oh no!''\<rrangle> ) \<rbrakk>\<close>
end

subsubsection\<open>HOL Value Injection (Antiquotation)\<close>

term\<open>\<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close>

subsection\<open>Type Casts and Ascriptions\<close>

subsubsection\<open>Type Casting\<close>

context
  fixes a_value :: \<open>32 word\<close>
begin
term\<open>\<lbrakk> a_value as u8\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u16\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u32\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u64\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u64; a_value as u64\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as usize\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as i32\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as i64\<rbrakk>\<close>
end

subsubsection\<open>Numeric Ascriptions\<close>

term \<open>\<lbrakk> 0_u8 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u8 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x4_u8 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_u16 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u16 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x12_u16 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_u32 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u32 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x2000_u32 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_u64 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u64 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x2f0_u64 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_usize \<rbrakk>\<close>
term \<open>\<lbrakk> 1_usize \<rbrakk>\<close>
term \<open>\<lbrakk> 0xffffffff0_usize \<rbrakk>\<close>

subsection\<open>Boolean Operators\<close>

subsubsection\<open>Boolean Negation\<close>

term\<open>\<lbrakk> !True \<rbrakk>\<close>
term\<open>\<lbrakk> !False \<rbrakk>\<close>
term\<open>\<lbrakk> !!True \<rbrakk>\<close>

term\<open>\<lbrakk>
  if !True {
    return;
  }
\<rbrakk>\<close>

subsubsection\<open>Boolean Conjunction\<close>

term\<open>\<lbrakk> True && True \<rbrakk>\<close>
term\<open>\<lbrakk> True && False \<rbrakk>\<close>
term\<open>\<lbrakk> False && True \<rbrakk>\<close>
term\<open>\<lbrakk> False && False \<rbrakk>\<close>

subsubsection\<open>Boolean Disjunction\<close>

term\<open>\<lbrakk> True || True \<rbrakk>\<close>
term\<open>\<lbrakk> True || False \<rbrakk>\<close>
term\<open>\<lbrakk> False || True \<rbrakk>\<close>
term\<open>\<lbrakk> False || False \<rbrakk>\<close>

term\<open>\<lbrakk>
  if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) {
    \<epsilon>\<open>\<up>0\<close>
  } else {
    \<epsilon>\<open>\<up>0\<close>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if True || !True {
    {{{{{{{{{{
      42
    }}}}}}}}}}
  } else {
    0
  }
\<rbrakk>\<close>

subsection\<open>Comparison Operators\<close>

subsubsection\<open>Equality and Nonequality\<close>

context
  fixes m n :: \<open>nat\<close>
  fixes h :: \<open>nat \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes x y :: \<open>64 word\<close>
begin
term \<open>\<lbrakk> m == n \<rbrakk>\<close>
term \<open>\<lbrakk> !(m == n) \<rbrakk>\<close>
term \<open>\<lbrakk> m != n \<rbrakk>\<close>
term \<open>\<lbrakk> m.h() \<rbrakk>\<close>
term \<open>\<lbrakk> if m.h() == n { m } else { n } \<rbrakk>\<close>
end

subsubsection\<open>Ordering Comparisons\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> x < y \<rbrakk>\<close>
term \<open>\<lbrakk> x <= y \<rbrakk>\<close>
term \<open>\<lbrakk> x > y \<rbrakk>\<close>
term \<open>\<lbrakk> x >= y \<rbrakk>\<close>
term \<open>\<lbrakk> x > \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>
end

subsection\<open>Arithmetic Operators\<close>

subsubsection\<open>Addition\<close>

term\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  let b = \<llangle>2 :: 32 word\<rrangle>;
  a + b
\<rbrakk>\<close>

context
  fixes x y :: \<open>64 word\<close>
begin
term\<open>\<lbrakk>
  let (a,b,c) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>);
  a + b + c
\<rbrakk>\<close>
end

subsubsection\<open>Subtraction\<close>

term\<open>\<lbrakk>
  let a = \<llangle>5 :: 32 word\<rrangle>;
  let b = \<llangle>3 :: 32 word\<rrangle>;
  a - b
\<rbrakk>\<close>

subsubsection\<open>Multiplication\<close>

term\<open>\<lbrakk>
  let a = \<llangle>3 :: 32 word\<rrangle>;
  let b = \<llangle>4 :: 32 word\<rrangle>;
  a * b
\<rbrakk>\<close>

subsubsection\<open>Division\<close>

term\<open>\<lbrakk>
  let a = \<llangle>12 :: 32 word\<rrangle>;
  let b = \<llangle>4 :: 32 word\<rrangle>;
  a / b
\<rbrakk>\<close>

subsubsection\<open>Modulo\<close>

term\<open>\<lbrakk>
  let a = \<llangle>17 :: 32 word\<rrangle>;
  let b = \<llangle>5 :: 32 word\<rrangle>;
  a % b
\<rbrakk>\<close>

subsection\<open>Bitwise Operators\<close>

subsubsection\<open>Bitwise AND\<close>

term\<open>\<lbrakk>
  let a = \<llangle>0xFF :: 32 word\<rrangle>;
  let b = \<llangle>0x0F :: 32 word\<rrangle>;
  a & b
\<rbrakk>\<close>

subsubsection\<open>Bitwise OR\<close>

term\<open>\<lbrakk>
  let a = \<llangle>0xF0 :: 32 word\<rrangle>;
  let b = \<llangle>0x0F :: 32 word\<rrangle>;
  a | b
\<rbrakk>\<close>

subsubsection\<open>Bitwise XOR\<close>

context
  fixes x y :: \<open>64 word\<close>
begin
term \<open>\<lbrakk> !x + y \<rbrakk>\<close>
term \<open>\<lbrakk> !(!x == x^y)  \<rbrakk>\<close>
end

term\<open>\<lbrakk>
  let a = \<llangle>0xFF :: 32 word\<rrangle>;
  let b = \<llangle>0x0F :: 32 word\<rrangle>;
  a ^ b
\<rbrakk>\<close>

subsubsection\<open>Bitwise NOT (Word Negation)\<close>

term\<open>\<lbrakk>
  let a = \<llangle>0x00 :: 8 word\<rrangle>;
  !a
\<rbrakk>\<close>

subsubsection\<open>Left Shift\<close>

term\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  a << \<llangle>4 :: 64 word\<rrangle>
\<rbrakk>\<close>

subsubsection\<open>Right Shift\<close>

term\<open>\<lbrakk>
  let a = \<llangle>16 :: 32 word\<rrangle>;
  a >> \<llangle>2 :: 64 word\<rrangle>
\<rbrakk>\<close>

subsection\<open>Assignment Operators\<close>

subsubsection\<open>Simple Assignment\<close>

context
  fixes r :: \<open>('s, 'b, integer) Global_Store.ref\<close>
begin

private definition dummy_dereference_assign :: \<open>('s, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference_assign \<equiv> undefined\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_assign

term \<open>\<lbrakk> r = 10 \<rbrakk>\<close>
term \<open>\<lbrakk> r = *r \<rbrakk>\<close>
term \<open>\<lbrakk> (r) = *r \<rbrakk>\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_assign
end

subsubsection\<open>Place Assignment Forms\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  (*x) = b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Add-Assign\<close>

context
  fixes a b :: \<open>'s\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x += b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Subtract-Assign\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x -= b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Multiply-Assign\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x *= b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Modulo-Assign\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x %= b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Bitwise Assign\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x |= b;
  *x
\<rbrakk>\<close>

term \<open>\<lbrakk>
  let mut x = a;
  x &= b;
  *x
\<rbrakk>\<close>

term \<open>\<lbrakk>
  let mut x = a;
  x ^= b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Shift-Assign\<close>

context
  fixes a :: \<open>32 word\<close>
  fixes b :: \<open>64 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x <<= b;
  *x
\<rbrakk>\<close>

term \<open>\<lbrakk>
  let mut x = a;
  x >>= b;
  *x
\<rbrakk>\<close>
end

subsection\<open>Control Flow - Conditionals\<close>

subsubsection\<open>Two-Armed Conditionals\<close>

term\<open>\<lbrakk>
  if True {
    return True;
  } else {
    return True;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if \<llangle>True\<rrangle> {
    let v = 16;
    return v;
  } else {
    42
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  ((if True { 0 } else { 1 }, True), if False { (2 as u32, 3 as u32) } else { (4, 5) })
\<rbrakk>\<close>

subsubsection\<open>Else-If Conditionals\<close>

term\<open>\<lbrakk>
  if False {
    \<llangle>0 :: 32 word\<rrangle>
  } else if True {
    \<llangle>1 :: 32 word\<rrangle>
  } else {
    \<llangle>2 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if False {
    \<llangle>0 :: 32 word\<rrangle>
  } else if False {
    \<llangle>1 :: 32 word\<rrangle>
  } else if True {
    \<llangle>2 :: 32 word\<rrangle>
  } else {
    \<llangle>3 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  assert!((if False { False } else if True { True } else { False }))
\<rbrakk>\<close>

subsubsection\<open>One-Armed Conditionals\<close>

term\<open>\<lbrakk>
  if True {
    ()
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(g) {
    return;
  }
\<rbrakk>\<close>

subsubsection\<open>Nested Conditionals\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(()) {
    if True {
      return;
    } else {
      return;
    }
  } else {
    return;
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  ((if True { 0 } else { 1 }, True), False)
\<rbrakk>\<close>

subsubsection\<open>Rust-Style Optional Semicolons for Block-Like Statements\<close>

term\<open>\<lbrakk>
  if True {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if True {
    ()
  } else {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if False {
    ()
  } else if True {
    ()
  } else {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(_) = Some(()) {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(_) = Some(()) {
    ()
  } else {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  match Some(()) {
    Some(_) \<Rightarrow> (),
    _ \<Rightarrow> ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # []\<rrangle>;
  for (a, b) in lst {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>(FunctionBody \<lbrakk>
  { () }
  ()
\<rbrakk>)\<close>

term\<open>\<lbrakk>
  unsafe { () }
  ()
\<rbrakk>\<close>

subsection\<open>Control Flow - If-Let and Let-Else\<close>

subsubsection\<open>If-Let with Option\<close>

term\<open>\<lbrakk>
  if let Some(_) = Some(()) {
    ()
  };
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(()) {
    return;
  } else {
    return;
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  if let Some((a, b)) = Some((\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>)) {
    assert!(a == \<llangle>1 :: 32 word\<rrangle>);
    assert!(b == \<llangle>2 :: 32 word\<rrangle>);
    ()
  } else {
    ()
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  if let Some(Some(x)) = Some(Some(\<llangle>3 :: 32 word\<rrangle>)) {
    assert!(x == \<llangle>3 :: 32 word\<rrangle>);
    ()
  } else {
    ()
  }
\<rbrakk>\<close>

subsubsection\<open>If-Let-Else\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(g) {
    return 0;
  } else {
    return 2;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let (a, b) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) {
    ()
  }
\<rbrakk>\<close>

subsubsection\<open>Let-Else with Option\<close>

term\<open>\<lbrakk>
  let (a, b) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) else {
    ()
  };
  ()
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let Some((a, b)) = Some((\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>)) else {
    ()
  };
  assert!(a == \<llangle>1 :: 32 word\<rrangle>);
  assert!(b == \<llangle>2 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>(FunctionBody \<lbrakk>
  let x = \<llangle>Some (0 :: nat)\<rrangle>;
  let Some(foo) = x else {
    assert!(False)
  };
  return;
\<rbrakk>)\<close>

context
  fixes n :: \<open>nat option\<close>
begin
term \<open>\<lbrakk> let Some(x) = n else { return \<llangle>5\<rrangle>; }; return x; \<rbrakk>\<close>
end

subsubsection\<open>Let-Else with Result\<close>

term\<open>\<lbrakk>
  let Ok(k) = Ok(()) else {
    return;
  };

  return k;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let Err(e) = Ok(()) else {
    return True;
  };

  return e;
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>7 :: 32 word\<rrangle>;
  let b = \<llangle>9 :: 32 word\<rrangle>;
  let Ok((x, y)) = Ok((a, b)) else {
    ()
  };
  assert!(x == a);
  assert!(y == b)
\<rbrakk>\<close>

subsubsection\<open>Let-Else with Tuples\<close>

value[simp]\<open>\<lbrakk>
  let (a,_) = (1,2);
  let (_,b) = (1,2);
  \<llangle>(a,b)\<rrangle>
\<rbrakk>\<close>

subsection\<open>Control Flow - Match Expressions\<close>

subsubsection\<open>Basic Match on Option\<close>

term\<open>\<lbrakk>
  match Some(x) {
    Some(y) \<Rightarrow> { return; },
    None \<Rightarrow> { return; }
  };
\<rbrakk>\<close>

term\<open>\<lbrakk>
  match Some(x) {
   None \<Rightarrow> { return; },
   Some(y) \<Rightarrow> y
  };
\<rbrakk>\<close>

subsubsection\<open>Match on Result\<close>

value[simp]\<open>\<lbrakk>
  let v = match Err(\<llangle>5 :: 32 word\<rrangle>) {
    Ok(_) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>,
    Err(x) \<Rightarrow> x
  };
  assert!(v == \<llangle>5 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Wildcard Patterns\<close>

term\<open>\<lbrakk>
  let _ = 3;
  let _ = (if True { False} else {True});
  const _ = {
    assert!(True);
    assert!(False);
  };
  let _ = assert!(let _ = False; if let Some(_) = None { False} else {True});
  match Some(a) {
    Some(_) \<Rightarrow> (),
    _ \<Rightarrow> ()
  };
  if let Some(_) = Some(()) {
    ()
  };
  ()
\<rbrakk>\<close>

subsubsection\<open>Variable Binding in Patterns\<close>

value[simp]\<open>\<lbrakk>
  let two = \<llangle>2 :: 32 word\<rrangle>;
  let res = match Some(Some(two)) {
    Some(Some(x)) \<Rightarrow> x,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == two)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let x = \<llangle>9 :: 32 word\<rrangle>;
  let y = match x {
    z \<Rightarrow> z
  };
  assert!(y == x)
\<rbrakk>\<close>

subsubsection\<open>Grouped and Irrefutable Patterns\<close>

value[simp]\<open>\<lbrakk>
  let v = match Some(\<llangle>5 :: 32 word\<rrangle>) {
    (Some(x)) \<Rightarrow> x,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(v == \<llangle>5 :: 32 word\<rrangle>)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let foo = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>);
  let (x, y) = foo;
  assert!(x == \<llangle>1 :: 32 word\<rrangle>);
  assert!(y == \<llangle>2 :: 32 word\<rrangle>)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let x = \<llangle>7 :: 32 word\<rrangle>;
  if let Some(y) = Some(x) {
    assert!(y == x);
    ()
  } else {
    assert!(False);
    ()
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let foo = (\<llangle>3 :: 32 word\<rrangle>, \<llangle>4 :: 32 word\<rrangle>);
  let (x, y) = foo else {
    ()
  };
  assert!(x == \<llangle>3 :: 32 word\<rrangle>);
  assert!(y == \<llangle>4 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Slice Patterns\<close>

term\<open>\<lbrakk>
  let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>;
  let res = match xs {
    [a, b, c] \<Rightarrow> a + b + c,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == \<llangle>6 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>;
  let tag = match xs {
    [_, _] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(tag == \<llangle>0 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let ys = \<llangle>([] :: 32 word list)\<rrangle>;
  let tag = match ys {
    [] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(tag == \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let [a, b] = \<llangle>[7 :: 32 word, 8]\<rrangle> {
    assert!(a == \<llangle>7 :: 32 word\<rrangle>);
    assert!(b == \<llangle>8 :: 32 word\<rrangle>);
    ()
  } else {
    assert!(False);
    ()
  }
\<rbrakk>\<close>

subsubsection\<open>Extended Rust-Style Pattern Forms\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>True\<rrangle> {
    true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    false \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>String.implode ''ok''\<rrangle> {
    "ok" \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>CHR ''a''\<rrangle> {
    \<llangle>CHR ''a''\<rrangle> \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match Some(\<llangle>7 :: 32 word\<rrangle>) {
    whole @ Some(v) \<Rightarrow> v,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

text\<open>Note: Rust-style pattern binders @{text "ref p"} and @{text "ref mut p"} are currently
not supported in this frontend, because they conflict with existing syntax around references
and function parameters in this Isabelle embedding.\<close>

term\<open>\<lbrakk>
  let y = match Some(\<llangle>7 :: 32 word\<rrangle>) {
    Some(&v) \<Rightarrow> v,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match Some(\<llangle>7 :: 32 word\<rrangle>) {
    Some(& mut v) \<Rightarrow> v,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

text\<open>Range patterns are lowered in the shallow embedding, but concrete parser-level
coverage for the Rust-style syntax is exercised separately in frontend-focused tests.\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>[7 :: 32 word, 8, 9]\<rrangle> {
    [head, ..] \<Rightarrow> head,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

text\<open>Current slice-rest lowering is partial: patterns with a suffix after @{text ".."}
elaborate, but only the prefix before @{text ".."} is currently enforced.\<close>
term\<open>\<lbrakk>
  match \<llangle>[1 :: 32 word, 2, 3, 4]\<rrangle> {
    [a, b, .., z] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

subsubsection\<open>Nested Patterns\<close>

value[simp]\<open>\<lbrakk>
  let one = \<llangle>1 :: 32 word\<rrangle>;
  let zero = \<llangle>0 :: 32 word\<rrangle>;
  assert!((match Some(Some(None)) {
    Some(None) \<Rightarrow> one,
    _ \<Rightarrow> zero
  }) == zero)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  let b = \<llangle>2 :: 32 word\<rrangle>;
  let c = \<llangle>3 :: 32 word\<rrangle>;
  let res = match ((a, b), c) {
    ((x, y), z) \<Rightarrow> (x, y, z)
  };
  assert!(res.0 == a);
  assert!(res.1 == b);
  assert!(res.2 == c)
\<rbrakk>\<close>

subsubsection\<open>Tuple Patterns in Match\<close>

datatype struct_pattern_fixture = Foo (foo: "32 word") (goo: "32 word") | Other

datatype_record struct_pattern_dr =
  dr_foo :: "32 word"
  dr_goo :: "32 word"

record struct_pattern_rec =
  rec_foo :: "32 word"
  rec_goo :: "32 word"

definition foo_struct_expr_lift where
  "foo_struct_expr_lift \<equiv> lift_fun2 Foo"

notation_nano_rust_function foo_struct_expr_lift ("Foo")

definition struct_pattern_dr_struct_expr_lift where
  "struct_pattern_dr_struct_expr_lift \<equiv> lift_fun2 make_struct_pattern_dr"

notation_nano_rust_function struct_pattern_dr_struct_expr_lift ("struct_pattern_dr")

term\<open>\<lbrakk>
  match (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) {
    (a, b) \<Rightarrow> a
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  let b = \<llangle>2 :: 32 word\<rrangle>;
  let c = \<llangle>3 :: 32 word\<rrangle>;
  let res = match Some((a, b, c)) {
    Some((x, _, z)) \<Rightarrow> (x, z),
    _ \<Rightarrow> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>0 :: 32 word\<rrangle>)
  };
  assert!(res.0 == a);
  assert!(res.1 == c)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>4 :: 32 word\<rrangle>;
  let b = \<llangle>8 :: 32 word\<rrangle>;
  if let Some((_, y)) = Some((a, b)) {
    assert!(y == b);
    ()
  } else {
    ()
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  let b = \<llangle>2 :: 32 word\<rrangle>;
  let c = \<llangle>3 :: 32 word\<rrangle>;
  let d = \<llangle>4 :: 32 word\<rrangle>;
  let res = match ((a, b), (c, d)) {
    ((w, x), (y, z)) \<Rightarrow> (w, x, y, z)
  };
  assert!(res.0 == a);
  assert!(res.1 == b);
  assert!(res.2 == c);
  assert!(res.3 == d)
\<rbrakk>\<close>

subsubsection\<open>Struct Patterns\<close>

term\<open>\<lbrakk>
  match \<llangle>Foo (1 :: 32 word) 2\<rrangle> {
    Foo { foo: p, goo: q } \<Rightarrow> p + q,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let res = match \<llangle>Foo (3 :: 32 word) 4\<rrangle> {
    Foo { foo: p, goo: q } \<Rightarrow> p + q,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Foo { foo: p, goo: q } = \<llangle>Foo (5 :: 32 word) 6\<rrangle> {
    assert!(p == \<llangle>5 :: 32 word\<rrangle>);
    assert!(q == \<llangle>6 :: 32 word\<rrangle>);
    ()
  } else {
    assert!(False);
    ()
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let Foo { foo: p, goo: q } = \<llangle>Foo (8 :: 32 word) 9\<rrangle> else {
    return;
  };
  p + q
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let res = match \<llangle>make_struct_pattern_dr (10 :: 32 word) 11\<rrangle> {
    struct_pattern_dr { dr_goo: q, dr_foo: p } \<Rightarrow> p + q
  };
  assert!(res == \<llangle>21 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> {
    Foo { foo, goo } \<Rightarrow> foo + goo,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == \<llangle>46 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> {
    Foo { foo, .. } \<Rightarrow> foo,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == \<llangle>12 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Struct Expressions\<close>

term\<open>\<lbrakk>
  Foo { foo: \<llangle>1 :: 32 word\<rrangle>, goo: \<llangle>2 :: 32 word\<rrangle> }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  Foo { goo: \<llangle>2 :: 32 word\<rrangle>, foo: \<llangle>1 :: 32 word\<rrangle> }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  struct_pattern_dr { dr_goo: \<llangle>11 :: 32 word\<rrangle>, dr_foo: \<llangle>10 :: 32 word\<rrangle> }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  Foo { foo: \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, goo: \<llangle>4 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> }
\<rbrakk>\<close>

subsubsection\<open>Pattern Guards\<close>

term\<open>\<lbrakk>
  match Some(x) {
    Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  match Some(x) {
    Some(y) if (if True { True } else { False }) \<Rightarrow> y,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let zero = \<llangle>0 :: 32 word\<rrangle>;
  let one = \<llangle>1 :: 32 word\<rrangle>;
  let res = match Some(one) {
    Some(x) if x > zero \<Rightarrow> x,
    _ \<Rightarrow> zero
  };
  assert!(res == one)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let zero = \<llangle>0 :: 32 word\<rrangle>;
  let res = match Some(zero) {
    Some(x) if x > zero \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    Some(x) \<Rightarrow> x,
    _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>
  };
  assert!(res == zero)
\<rbrakk>\<close>

subsubsection\<open>Match with Return\<close>

term\<open>\<lbrakk>
  match Some(x) {
    Some(y) \<Rightarrow> { return; },
    None \<Rightarrow> { return; }
  };
\<rbrakk>\<close>

subsubsection\<open>Numeric Match (match_switch)\<close>

text\<open>See Section 21 (Rust Path Expressions) for match_switch examples\<close>

subsection\<open>Control Flow - Loops\<close>

subsubsection\<open>Basic For Loop\<close>

term\<open>\<lbrakk>
  let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # (3, 4, TNil) # []\<rrangle>;
  for (a, b) in lst {
    let _ = a;
    let _ = b;
    ()
  };
  ()
\<rbrakk>\<close>

subsubsection\<open>For Loop with Tuple Destructuring\<close>

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  let lst = \<llangle>(1, 2, (True, False, ()), ()) # (1, 2, (True, False, ()), ()) # []\<rrangle>;
  for i in lst {
    if (i.2.0) && i.2.1 {
      *x = i.0;
    } else {
      *x = i.1;
    }
  };
  x
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  let lst = \<llangle>(1, 2, (True, False, nil), nil) # (1, 2, (True, False, nil), nil) # []\<rrangle>;
  for (a, b, (c, d)) in lst {
    if c && d {
      x += a;
    } else {
      x += b;
    }
  };
  x
\<rbrakk>\<close>

subsubsection\<open>For Loop with Range\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> for i in x .. y { () } \<rbrakk>\<close>
end

subsection\<open>Control Flow - Return\<close>

subsubsection\<open>Return Without Value\<close>

term\<open>\<lbrakk>
  return;
\<rbrakk>\<close>

term\<open>(FunctionBody \<lbrakk>
  {return;}; return;
\<rbrakk>)\<close>

subsubsection\<open>Return With Value\<close>

term\<open>\<lbrakk>
  let v = \<llangle>42 :: 64 word\<rrangle>;
  return v;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let (a,b) = (1,2);
  return;
\<rbrakk>\<close>

subsubsection\<open>Return in Control Flow\<close>

definition test :: \<open>(nat, unit, unit, unit, unit) function_body\<close> where
  \<open>test \<equiv> (FunctionBody \<lbrakk>
    let x = \<llangle>Some (0 :: nat)\<rrangle>;
    let Some(foo) = x else {
      return;
    };
    return;
  \<rbrakk>)\<close>
hide_const test

term\<open>(FunctionBody \<lbrakk>
    let x = \<llangle>Some (0 :: nat)\<rrangle>;
    let Some(foo) = x else {
      return;
    };
    return;
  \<rbrakk>) :: (nat, unit, unit, unit, unit) function_body\<close>

context
  fixes x :: \<open>'s\<close>
  fixes g :: \<open>'s \<Rightarrow> ('a, nat option, unit, unit, unit) function_body\<close>
begin
term\<open>\<lbrakk>
  let blub = 0;
  if let Some(x) = g(x) {
    return 0;
  } else {
    return 42;
  };
  return 12;
\<rbrakk>\<close>
end

\<comment> \<open>Having a warning in the following test case is expected, see also RFC:
\<^url>\<open>https://rust-lang.github.io/rfcs/3137-let-else.html\<close>\<close>
term\<open>\<lbrakk>
  let x = if True { 0 } else { 1 };
  return x;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let x = (if True { 0 } else { 1 });
  return x;
\<rbrakk>\<close>

subsection\<open>Control Flow - Error Propagation\<close>

subsubsection\<open>Propagation with Option\<close>

context
  fixes opt :: \<open>nat option\<close>
begin
term \<open>\<lbrakk> opt? \<rbrakk>\<close>
term \<open>\<lbrakk> let x = opt?; x \<rbrakk>\<close>
end

subsubsection\<open>Propagation with Result\<close>

context
  fixes res :: \<open>(nat, bool) result\<close>
begin
term \<open>\<lbrakk> res? \<rbrakk>\<close>
term \<open>\<lbrakk> let x = res?; x \<rbrakk>\<close>
end

subsection\<open>Data Structures - Tuples\<close>

subsubsection\<open>Tuple Construction\<close>

value[simp]\<open>\<lbrakk>
  (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, True, False)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  ((False, True), False)
\<rbrakk>\<close>

subsubsection\<open>Tuple Indexing\<close>

value[simp]\<open>\<lbrakk>
  assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == \<llangle>0 :: 32 word\<rrangle>);
  assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).1 == \<llangle>1 :: 32 word\<rrangle>);
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>0 :: 32 word\<rrangle>;
  let b = \<llangle>1 :: 32 word\<rrangle>;
  let c = \<llangle>2 :: 32 word\<rrangle>;
  let d = \<llangle>3 :: 32 word\<rrangle>;
  let e = \<llangle>4 :: 32 word\<rrangle>;
  let f = \<llangle>5 :: 32 word\<rrangle>;
  let g = \<llangle>6 :: 32 word\<rrangle>;
  let h = \<llangle>7 :: 32 word\<rrangle>;
  let tup = (a, b, c, d, e, f, g, h);
  assert!(tup.0 == 0);
  assert!(tup.1 == 1);
  assert!(tup.2 == 2);
  assert!(tup.3 == 3);
  assert!(tup.4 == 4);
  assert!(tup.5 == 5);
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let tup = (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>,
             \<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>, \<llangle>6 :: 32 word\<rrangle>, \<llangle>7 :: 32 word\<rrangle>,
             \<llangle>8 :: 32 word\<rrangle>, \<llangle>9 :: 32 word\<rrangle>, \<llangle>10 :: 32 word\<rrangle>, \<llangle>11 :: 32 word\<rrangle>,
             \<llangle>12 :: 32 word\<rrangle>, \<llangle>13 :: 32 word\<rrangle>, \<llangle>14 :: 32 word\<rrangle>, \<llangle>15 :: 32 word\<rrangle>);
  assert!(tup.6 == \<llangle>6 :: 32 word\<rrangle>);
  assert!(tup.10 == \<llangle>10 :: 32 word\<rrangle>);
  assert!(tup.15 == \<llangle>15 :: 32 word\<rrangle>)
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>0 :: 32 word\<rrangle>;
  let b = \<llangle>1 :: 32 word\<rrangle>;
  let c = \<llangle>2 :: 32 word\<rrangle>;
  let tup = (a, b, c, (False, True));
  assert!(tup.0 == 0);
  assert!(tup.1 == 1);
  assert!(tup.2 == 2);
  assert!(tup.3.0 == False);
  assert!(tup.3.1 == True);
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == 0)
\<rbrakk>\<close>

(*
TODO: Fix this bug
lemma \<open>\<lbrakk>assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == 0)\<rbrakk> = Expression (Success ())\<close>
  by simp
*)

subsubsection\<open>Tuple Destructuring\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>0 :: 32 word\<rrangle>;
  let b = \<llangle>1 :: 32 word\<rrangle>;
  let c = \<llangle>2 :: 32 word\<rrangle>;
  let d = \<llangle>3 :: 32 word\<rrangle>;
  let e = \<llangle>4 :: 32 word\<rrangle>;
  let f = \<llangle>5 :: 32 word\<rrangle>;
  let g = \<llangle>6 :: 32 word\<rrangle>;
  let h = \<llangle>7 :: 32 word\<rrangle>;
  let tup = (a, b, c, d, e, f, g, h);
  let (aa, bb, cc, dd, ee, ff, gg, hh) = tup;
  assert!(a == aa);
  assert!(b == bb);
  assert!(c == cc);
  assert!(d == dd);
  assert!(e == ee);
  assert!(f == ff);
  assert!(g == gg);
  assert!(h == hh);
  let tup2 = (a, (b, c));
  let (aaa, (bbb, ccc)) = tup2;
  assert!(aaa == a);
  assert!(bbb == b);
  assert!(ccc == c);
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let a = \<llangle>10 :: 32 word\<rrangle>;
  let b = \<llangle>20 :: 32 word\<rrangle>;
  let c = \<llangle>30 :: 32 word\<rrangle>;
  let tup = (a, (b, c));
  let (x, (y, z)) = tup;
  assert!(x == a);
  assert!(y == b);
  assert!(z == c)
\<rbrakk>\<close>

subsection\<open>Data Structures - Option and Result\<close>

subsubsection\<open>Option Construction\<close>

term\<open>\<lbrakk> Some(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close>
term\<open>\<lbrakk> None \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close>

subsubsection\<open>Result Construction\<close>

term\<open>\<lbrakk> Ok(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close>
term\<open>\<lbrakk> Err(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close>

subsubsection\<open>Option/Result in Pattern Matching\<close>

text\<open>See earlier sections on match expressions for comprehensive examples.\<close>

subsection\<open>Data Structures - Ranges\<close>

subsubsection\<open>Exclusive Range\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> x..y \<rbrakk>\<close>
end

subsubsection\<open>Inclusive Range\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> x..=y \<rbrakk>\<close>
term \<open>\<lbrakk> let rng = x ..= x+y; rng.is_empty() \<rbrakk>\<close>
end

subsubsection\<open>Inclusive Range Boundary Behavior\<close>

value[simp]\<open>\<lbrakk>
  let int_max = \<llangle>255 :: 8 word\<rrangle>;
  let inclusive = int_max ..= int_max;
  assert!(!(inclusive.is_empty()));
  assert!(inclusive.contains(int_max));
  let exclusive = int_max .. int_max;
  assert!(exclusive.is_empty());
  ()
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let mut count = \<llangle>0 :: 8 word\<rrangle>;
  let int_max = \<llangle>255 :: 8 word\<rrangle>;
  for i in int_max ..= int_max {
    count += \<llangle>1 :: 8 word\<rrangle>;
  };
  assert!(*count == \<llangle>1 :: 8 word\<rrangle>);
  ()
\<rbrakk>\<close>

subsubsection\<open>Range in For Loops\<close>

text\<open>See For Loop with Range subsection above.\<close>

subsection\<open>Functions and Closures\<close>

subsubsection\<open>Function Calls\<close>

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
  fixes h :: \<open>'s \<Rightarrow> 't \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes i :: \<open>'s \<Rightarrow> 't \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
begin

term\<open>\<lbrakk>
  h(a, b, c, a)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  i(a, b, c, a, b)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  \<epsilon>\<open>g\<close>(c);
  g(c);
  f(a,b);
  a.f(b);
  f(g(c),b);
  g(c).f(b)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  f(g(c),b)
\<rbrakk>\<close>

end

subsubsection\<open>Method-Style Calls\<close>

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
begin

term\<open>\<lbrakk>
  g(c);
  c.g();
\<rbrakk>\<close>

term\<open>\<lbrakk>
  a.f(b)
\<rbrakk>\<close>

end

subsubsection\<open>Turbofish Syntax\<close>

context
  fixes f :: \<open>nat \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
term \<open>\<lbrakk> f::<5>() \<rbrakk>\<close>
term \<open>\<lbrakk> g::<10>(True) \<rbrakk>\<close>
end

subsubsection\<open>Closures\<close>

context
  fixes f :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes h :: \<open>nat \<Rightarrow> (bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body) \<Rightarrow> ('s, unit, unit, unit, unit) function_body\<close>
  fixes n :: \<open>nat\<close>
begin
term \<open>\<lbrakk> || return x; \<rbrakk>\<close>
term \<open>\<lbrakk> |x| x \<rbrakk>\<close>
term \<open>\<lbrakk> |x, y| { let z = f(x,y); return z; }  \<rbrakk>\<close>
term \<open>\<lbrakk> h(n, |b| { let z = f(n,b); return \<llangle>n+z\<rrangle>; }) \<rbrakk>\<close>
end

subsection\<open>References and Mutation\<close>

subsubsection\<open>Mutable Bindings\<close>

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  x
\<rbrakk>\<close>

subsubsection\<open>Borrow Syntax\<close>

context
  fixes r :: \<open>('s, 'b, integer) Global_Store.ref\<close>
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> &r \<rbrakk>\<close>
term \<open>\<lbrakk> &mut r \<rbrakk>\<close>
term \<open>\<lbrakk> x & y \<rbrakk>\<close>
end

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  let xr = &x;
  let xw = &mut x;
  xw
\<rbrakk>\<close>

subsubsection\<open>Dereference\<close>

context
  fixes r :: \<open>('s, 'b, integer) Global_Store.ref\<close>
begin

private definition dummy_dereference_ref :: \<open>('s, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference_ref \<equiv> undefined\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_ref

term \<open>\<lbrakk> *r \<rbrakk>\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_ref
end

subsubsection\<open>Double Dereference\<close>

context
  fixes rr :: \<open>('s, 'b, ('s, 'b, integer) Global_Store.ref) Global_Store.ref\<close>
begin

private definition dummy_dereference_ref2 :: \<open>('s, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference_ref2 \<equiv> undefined\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_ref2

term \<open>\<lbrakk> **rr \<rbrakk>\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_ref2
end

subsubsection\<open>Assignment\<close>

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  *x = \<llangle>42 :: 32 word\<rrangle>;
  x
\<rbrakk>\<close>

subsection\<open>Field Access and Records\<close>

subsubsection\<open>Test Record Definitions\<close>

datatype_record testrec =
  field1 :: integer
  field2 :: bool
micro_rust_record testrec

datatype_record testrec2 =
  field3 :: testrec
  field4 :: \<open>bool option\<close>
micro_rust_record testrec2

subsubsection\<open>Simple Field Access\<close>

context
  fixes x :: testrec
  fixes y :: testrec2
begin
term\<open> \<lbrakk> x \<rbrakk> \<close>
term \<open>\<lbrakk> x.field1 \<rbrakk>\<close>
term \<open>\<lbrakk> y.field4 \<rbrakk>\<close>
end

subsubsection\<open>Nested Field Access\<close>

context
  fixes y :: testrec2
begin
value \<open>\<lbrakk> y.field3.field1 \<rbrakk>\<close>
end

subsubsection\<open>Field Assignment Through Lenses\<close>

context
  fixes r :: \<open>('s, 'b, integer) Global_Store.ref\<close>
  fixes s :: \<open>('s, 'b, testrec2) Global_Store.ref\<close>
  fixes f :: \<open>('s, 'b, integer) Global_Store.ref \<Rightarrow> integer \<Rightarrow> ('s, unit, unit, unit, unit) function_body\<close>
begin

private definition dummy_dereference_field :: \<open>('s, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference_field \<equiv> undefined\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_field

term\<open>field4_lens\<close>
term \<open>\<lbrakk> r.f(10) \<rbrakk>\<close>
term\<open>bindlift2 focus_const (literal s) (literal field3_lens)\<close>
term \<open>\<lbrakk> *(s. field3_lens) \<rbrakk>\<close>
term\<open>store_dereference_const s\<close>
term \<open>\<lbrakk> (*s). field3_lens \<rbrakk>\<close>
term \<open>\<lbrakk> *r \<rbrakk>\<close>
term \<open>\<lbrakk> r = *r \<rbrakk>\<close>
term \<open>\<lbrakk> r = (*s).field3_lens.field1_lens \<rbrakk>\<close>
term \<open>\<lbrakk> r = *s.field3_lens.field1_lens \<rbrakk>\<close>

term \<open>\<lbrakk> r = 10 \<rbrakk>\<close>
term \<open>\<lbrakk> *(s.field4_lens) \<rbrakk>\<close>
term \<open>\<lbrakk> (*s).field4_lens \<rbrakk>\<close>
term \<open>\<lbrakk> s.field3_lens.field1_lens = *r \<rbrakk>\<close>
term \<open>\<lbrakk> *r \<rbrakk>\<close>

term \<open>\<lbrakk> s.field3_lens \<rbrakk>\<close>
term \<open>\<lbrakk> s.field3_lens.field2_lens \<rbrakk>\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_field
end

subsection\<open>Macros\<close>

subsubsection\<open>Assertion Macros\<close>

context
  fixes b :: \<open>bool\<close>
  fixes o :: \<open>nat option\<close>
  fixes a_value :: \<open>32 word\<close>
  fixes x y :: \<open>nat\<close>
begin
term \<open>\<lbrakk> assert!( b ) \<rbrakk>\<close>
term \<open>\<lbrakk> debug_assert!( b ) \<rbrakk>\<close>
term \<open>\<lbrakk> assert!(!o.is_none()) \<rbrakk>\<close>
term\<open>\<lbrakk> assert!(b); a_value as u16\<rbrakk>\<close>
term\<open>\<lbrakk> assert!(a_value as usize == a_value as usize); a_value as u16\<rbrakk>\<close>
term \<open>\<lbrakk> assert_eq!(x, y) \<rbrakk>\<close>
term \<open>\<lbrakk> assert_ne!(x, y) \<rbrakk>\<close>
term \<open>\<lbrakk> assert!(b, "ignored assertion message") \<rbrakk>\<close>
term \<open>\<lbrakk> debug_assert!(b, "ignored debug assertion message", x) \<rbrakk>\<close>
term \<open>\<lbrakk> assert_eq!(x, y, "ignored assert_eq message", x) \<rbrakk>\<close>
term \<open>\<lbrakk> assert_ne!(x, y, "ignored assert_ne message", y) \<rbrakk>\<close>
term \<open>\<lbrakk> debug_assert_eq!(x, y, "ignored debug_assert_eq message") \<rbrakk>\<close>
term \<open>\<lbrakk> debug_assert_ne!(x, y, "ignored debug_assert_ne message") \<rbrakk>\<close>
end

subsubsection\<open>Error Macros\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
term \<open>\<lbrakk> panic!(msg) \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!(msg) \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!("some_fun") \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!(nm) \<rbrakk>\<close>
term \<open>\<lbrakk> todo!("oh no!") \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!("yikes!") \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!( \<llangle>''yikes!''\<rrangle> ) \<rbrakk>\<close>
term \<open>\<lbrakk> panic!() \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!() \<rbrakk>\<close>
term \<open>\<lbrakk> todo!() \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!() \<rbrakk>\<close>
term \<open>\<lbrakk> panic!("first", msg) \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!("first", msg) \<rbrakk>\<close>
term \<open>\<lbrakk> todo!("first", msg) \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!("first", msg) \<rbrakk>\<close>
end

subsubsection\<open>Logging\<close>

context
  fixes b :: \<open>bool\<close>
begin
term \<open>\<lbrakk> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 32]\<rrangle> \<rbrakk>\<close>
term \<open>\<lbrakk> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat 32, LogString (String.implode ''goo'')]\<rrangle> \<rbrakk>\<close>
term \<open>\<lbrakk> \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>[LogBool b]\<rrangle> \<rbrakk>\<close>
end

subsection\<open>Miscellaneous Features\<close>

subsubsection\<open>Unsafe Blocks\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
term \<open>\<lbrakk> unsafe { panic!("msg") } \<rbrakk>\<close>
end

subsubsection\<open>Array and Slice Expression Literals\<close>

term \<open>\<lbrakk> [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close>
term \<open>\<lbrakk> &[\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close>
term \<open>\<lbrakk> & mut [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close>
term \<open>\<lbrakk> & mut [] \<rbrakk>\<close>
term \<open>\<lbrakk> [\<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let xs = [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>];
  assert!(xs[0] == \<llangle>1 :: 32 word\<rrangle>);
  assert!(xs[2] == \<llangle>3 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let xs = &[\<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>];
  let s = match xs {
    [a, b] \<Rightarrow> a + b,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(s == \<llangle>9 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Indexing\<close>

context
  fixes xs :: \<open>nat list\<close>
  fixes xss :: \<open>nat list list\<close>
begin
term \<open>\<lbrakk> xs [0..100][42] \<rbrakk>\<close>
term \<open>\<lbrakk> xss[10] \<rbrakk>\<close>
term \<open>\<lbrakk> xss[10][100] \<rbrakk>\<close>
end

subsubsection\<open>Const Bindings\<close>

term\<open>\<lbrakk>
  const FOO = 5;
  ()
\<rbrakk>\<close>

subsubsection\<open>Scoping and Block Expressions\<close>

context
  fixes x :: \<open>'s\<close>
begin
term\<open>\<lbrakk> 1 \<rbrakk> :: ('s, nat, 'r, 'abort, 'i, 'o) expression\<close>
end

subsubsection\<open>Sequencing\<close>

term\<open>\<lbrakk>
  let a = 1;
  let b = 2;
  a
\<rbrakk>\<close>

subsection\<open>Rust Path Expressions\<close>

text\<open>Experiment block with path notation tests\<close>

experiment
  notes [[syntax_ast_trace]]
begin

term\<open>3 :: 64 word\<close>

definition number_42 :: nat where \<open>number_42 \<equiv> 42\<close>

notation_nano_rust number_42 ("foo::bar::test1")
notation_nano_rust number_42 ("foo::bar::test2")
notation_nano_rust True ("foo::bar::test3")

definition \<open>the_record \<equiv> make_testrec 1 False\<close>

notation_nano_rust the_record ("the::record")

term\<open>\<lbrakk>the::record\<rbrakk>\<close>
term\<open>\<lbrakk>(the::record).field1\<rbrakk>\<close>
term\<open>\<lbrakk>the::record.field1\<rbrakk>\<close>

term\<open>(1, 2)\<close>

term\<open>\<lbrakk> foo::bar::test1 \<rbrakk>\<close>
term\<open>\<lbrakk> foo::bar:: test2 \<rbrakk>\<close>
term\<open>\<lbrakk> foo:: bar::test3 \<rbrakk>\<close>

datatype test =
    Test1
  | Test2

notation_nano_rust test.Test1 ("test'::Test_1")
notation_nano_rust test.Test2 ("test::Test'_2")

definition plus_two :: \<open>'l::len word \<Rightarrow> 'l word\<close> where \<open>plus_two n \<equiv> n + 2\<close>
definition \<open>plus_two_lift \<equiv> lift_fun1 plus_two\<close>

notation_nano_rust plus_two_lift ("plus2::lifted")

definition three :: \<open>64 word\<close> where \<open>three = 3\<close>
notation_nano_rust three ("number::three")

term\<open>\<lbrakk> test::Test_1 \<rbrakk>\<close>

term\<open>\<lbrakk>plus2::lifted(three)\<rbrakk>\<close>
term\<open>\<lbrakk>plus_two_lift(three)\<rbrakk>\<close>

term\<open>\<lbrakk>
  let arg = test::Test_1;
  let fun = plus2::lifted;
  match arg {
    test::Test_1 \<Rightarrow> fun(three),
    test::Test_2 \<Rightarrow> plus2::lifted(three)
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let x = 5;
  match x {
    2 \<Rightarrow> False,
    number::three \<Rightarrow> False,
    0 \<Rightarrow> False,
    1 \<Rightarrow> False,
    _ \<Rightarrow> True
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let x = 5;
\<comment> \<open>\<^verbatim>\<open>match_switch\<close> forces interpretation of this \<^verbatim>\<open>match\<close> clause as a \<^verbatim>\<open>switch\<close>\<close>
  match_switch x {
    number::three \<Rightarrow> False,
    _ \<Rightarrow> True
  }
\<rbrakk>\<close>

end

subsection\<open>Disjunctive Patterns\<close>

text\<open>For testing non-exhaustive disjunctive patterns in @{text "if let"} and @{text "let else"},
we need a type with more than two constructors. Using @{type option} or @{type result} with
disjunctive patterns that cover all constructors causes HOL's case expression machinery to
complain about redundant clauses (the implicit wildcard fallback becomes unreachable).\<close>

datatype three_case = CaseA nat | CaseB nat | CaseC

subsubsection\<open>Basic Match with Disjunctive Pattern\<close>

term\<open>\<lbrakk>
  match Some(\<llangle>42 :: nat\<rrangle>) {
    Some(x) | None \<Rightarrow> x
  }
\<rbrakk>\<close>

subsubsection\<open>Multiple Alternatives\<close>

context
  fixes x :: \<open>32 word\<close>
begin
term\<open>\<lbrakk>
  match_switch x {
    1 | 2 | 3 \<Rightarrow> True,
    _ \<Rightarrow> False
  }
\<rbrakk>\<close>
end

subsubsection\<open>Disjunctive Pattern with Guard\<close>

context
  fixes x :: \<open>32 word option\<close>
begin
term\<open>\<lbrakk>
  match x {
    Some(y) | None if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>
end

subsubsection\<open>If-Let with Disjunctive Pattern\<close>

text\<open>Using @{type three_case} with only two alternatives ensures non-exhaustiveness,
so the implicit wildcard fallback is not redundant.\<close>

term\<open>\<lbrakk>
  if let CaseA(x) | CaseB(x) = \<llangle>CaseA 42\<rrangle> {
    ()
  }
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  if let CaseA(x) | CaseB(x) = \<llangle>CaseA 5\<rrangle> {
    assert!(x == \<llangle>5 :: nat\<rrangle>);
    ()
  } else {
    ()
  }
\<rbrakk>\<close>

subsubsection\<open>Let-Else with Disjunctive Pattern\<close>

text\<open>Using @{type three_case} ensures the disjunctive pattern is non-exhaustive.\<close>

term\<open>\<lbrakk>
  let CaseA(x) | CaseB(x) = \<llangle>CaseA 7\<rrangle> else {
    return;
  };
  x
\<rbrakk>\<close>

value[simp]\<open>\<lbrakk>
  let CaseA(x) | CaseB(x) = \<llangle>CaseB 10\<rrangle> else {
    ()
  };
  assert!(x == \<llangle>10 :: nat\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Nested Disjunctive Patterns\<close>

term\<open>\<lbrakk>
  match Some(Ok(\<llangle>1 :: nat\<rrangle>)) {
    Some(Ok(x) | Err(x)) \<Rightarrow> x,
    _ \<Rightarrow> \<llangle>0 :: nat\<rrangle>
  }
\<rbrakk>\<close>

subsubsection\<open>Match-Switch with Disjunctive Numeric Patterns\<close>

context
  fixes x :: \<open>64 word\<close>
begin
term\<open>\<lbrakk>
  match_switch x {
    0 | 1 \<Rightarrow> False,
    _ \<Rightarrow> True
  }
\<rbrakk>\<close>
end

subsubsection\<open>Disjunctive Pattern with Result\<close>

value[simp]\<open>\<lbrakk>
  let res = match Ok(\<llangle>10 :: 32 word\<rrangle>) {
    Ok(x) | Err(x) \<Rightarrow> x
  };
  assert!(res == \<llangle>10 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Multiple Disjunctions in One Match\<close>

term\<open>\<lbrakk>
  match (Some(\<llangle>1 :: nat\<rrangle>), Some(\<llangle>2 :: nat\<rrangle>)) {
    (Some(x), Some(y)) | (None, Some(y)) \<Rightarrow> y,
    _ \<Rightarrow> \<llangle>0 :: nat\<rrangle>
  }
\<rbrakk>\<close>

end
