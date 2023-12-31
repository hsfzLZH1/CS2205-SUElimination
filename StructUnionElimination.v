Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import PL.SyntaxInCoq.
Require Import PL.DenotationalSemantics.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(**可在课程 git 仓库 pl 文件夹下编译**)

(**主要定义及结论：**)
(**“Struct 和 Union 定义”的定义  SUDef**)
(**WhileDU1 的语法树定义  Module Lang_WhileDU1**)
(**WhileD+malloc 的语法树定义   Module Lang_WhileD_malloc**)
(**WhileDU1 的表达式指称语义   Module DntSem_WhileDU1 :: eval_l eval_r**)
(**WhileDU1 语义类型相关规定   Module EDenoteDU1. 下方**)
(**WhileDU1 从语法推断表达式求值结果类型的函数
   Module DntSem_WhileDU1 :: type_l type_r**)
(**WhileDU1 程序语句指称语义   Module DntSem_WhileDU1 :: eval_com**)
(**WhileD+malloc 的指称语义   Module DntSem_WhileD_malloc :: eval_l eval_r eval_com**)
(**表达式的精化关系   ERefineRel**)
(**表达式对应结构保持精化关系   EConst_persistRR -- EAddrOf_persistRR**)
(**给定 SUDef 和变量类型环境，同一表达式在任意程序状态下，正常求值结果的类型总是相同的，即 type_l type_r 从语法上推断出的类型
   WhileDU1_DntSemnrm_TypeEq**)
(**表达式的变换   ETransform**)
(**表达式的变换服从精化关系   ETransform_RefineRel**)
(**程序语句的精化关系   CRefineRel**)
(**程序语句对应结构保持精化关系   CSkip_RR -- CWhile_persistRR**)
(**程序语句的变换   CTransform**)
(**程序语句的变换服从精化关系   CTransform_RefineRel**)

Import Lang_SimpleWhile.

(**定义变量类型**)
Inductive Types: Type :=
| Int64: Types
| Struct (name:var_name): Types
| Union (name:var_name): Types
| Pointer (towards:Types): Types.

(**Struct 和 Union 成员的定义**)
Record Var_Def: Type := {
  type: Types;
  name: var_name;
}.

(**“Struct 和 Union 定义”的定义**)
(**option 为 None 表示没有对应名称的 Struct/Union**)
Definition Struct_Def:= var_name -> option (list Var_Def).
Definition Union_Def:= var_name -> option (list Var_Def).
Record SUDef: Type := {
  SDef: var_name -> option (list Var_Def);
  UDef: var_name -> option (list Var_Def);
  size: Types->Z;
}.

(**通过应满足的性质定义 sizeof 函数**)
(**该性质在后续证明中没有使用到，只需要一个 Types->Z 的 size 函数**)
Fixpoint sizeSum (ls:(list Var_Def)) (size:Types->Z): Z:=
  match ls with
  | nil => 0
  | cons vardef cdr => (size (type vardef))+(sizeSum cdr size)
  end.
Fixpoint sizeMax (ls:(list Var_Def)) (size:Types->Z): Z:=
  match ls with
  | nil => 0
  | cons vardef cdr => 
      if ((size (type vardef))<=?(sizeMax cdr size)) then (sizeMax cdr size) else (size (type vardef)) 
  end.
Definition is_sizeof (size:Types->Z) (sdef:Struct_Def) (udef:Union_Def): Prop :=
  forall s:Types,
    match s with
    | Int64 => (size s)=1
    | Pointer p => (size s)=1
    | Struct n =>
        match (sdef n) with
        | None => True
        | Some ls => (size s)=(sizeSum ls size)
        end
    | Union n =>
        match (udef n) with
        | None => True
        | Some ls => (size s)=(sizeMax ls size)
        end
    end.
Definition size_valid (def:SUDef): Prop := is_sizeof (size def) (SDef def) (UDef def).
Definition sizeof (t:Types) (def:SUDef): Z:= ((size def) t).

(**计算域中某个元素相对首地址的偏移量**)
Fixpoint calc_offset (ls:(list Var_Def)) (foc:var_name) (size:Types->Z): Z:=
  match ls with
  | nil => 0
  | cons vardef cdr =>
      if ((eqb (name vardef) foc)) then 0 
        else (calc_offset cdr foc size)+(size (type vardef))
  end.
(**t 为 Struct/Union 的类型**)
Definition offset (t:Types) (foc:var_name) (def:SUDef): Z:=
  match t with
  | Struct n => 
    match ((SDef def) n) with
    | None => 0
    | Some ls => (calc_offset ls foc (size def))
    end
  | _ => 0
  end.

Inductive val: Type :=
| Vuninit: val
| Vint (i: int64): val.

(**WhileDU1 和 WhileD+malloc 使用同一个程序状态定义**)
(**env 中 option 表示变量是否声明，若是记录变量的类型和首地址**)
(**mem 中，外层 option 表示地址是否可以被 malloc ，内层 option 表示地址是否有访问权限（已经被 malloc ）， val 表示可以被 malloc 且有访问权限的地址上的值是否初始化，若是则记录地址上的值**)
Record state: Type := {
  env: var_name -> option int64;
  mem: int64 -> option (option val);
}.
Notation "s '.(env)'" := (env s) (at level 1).
Notation "s '.(mem)'" := (mem s) (at level 1).

(**为变量 X 分配长为 len 的内存，首地址为 head 的过程的指称语义，在两种语言局部变量声明语句的指称语义中使用**)
(**可以正常分配的情况： (s1,s2) 二元关系， s1 中整段地址均可以被 malloc ，且还没有已经被 malloc ， s2 中已经 malloc 且没有初始化**)
Definition malloc_nrm (X: var_name) (len: int64) (head: int64) (s1 s2: state): Prop :=
  (Int64.unsigned len)+(Int64.unsigned head)<=Int64.max_unsigned /\
  s2.(env) X = Some head /\
  (forall t, ((Int64.unsigned len)<=t /\ t<=(Int64.unsigned len)+(Int64.unsigned head)-1) -> 
    s1.(mem) (Int64.repr t) = Some (None) /\
    s2.(mem) (Int64.repr t) = Some (Some (Vuninit))).

(**分配异常的情况**)
Definition malloc_invalid (X: var_name) (len: int64) (head: int64) (s1: state): Prop :=
  (Int64.unsigned len)+(Int64.unsigned head)>Int64.max_unsigned \/
  (exists t, ((Int64.unsigned len)<=t /\ t<=(Int64.unsigned len)+(Int64.unsigned head)-1) ->
    s1.(mem) (Int64.repr t) <> Some (None)).

(**分配前程序状态 s0 ，释放变量 X 首地址 head 长为 len 的内存段的指称语义， X 的地址恢复 s0 中状态**)
Definition free_nrm (X: var_name) (len: int64) (head: int64) (s0 s1 s2: state): Prop :=
  (Int64.unsigned len)+(Int64.unsigned head)<=Int64.max_unsigned /\
  s1.(env) X = Some head /\ s2.(env) X = s0.(env) X /\
  (forall t, ((Int64.unsigned len)<=t /\ t<=(Int64.unsigned len)+(Int64.unsigned head)-1) ->
    s1.(mem) (Int64.repr t) <> None /\ s1.(mem) (Int64.repr t) <> Some (None) /\
    s2.(mem) (Int64.repr t) = Some (None)).

Definition free_invalid (X: var_name) (len: int64) (head: int64) (s1: state): Prop :=
  (Int64.unsigned len)+(Int64.unsigned head)>Int64.max_unsigned \/
  s1.(env) X <> Some (head) \/
  (exists t, ((Int64.unsigned len)<=t /\ t<=(Int64.unsigned len)+(Int64.unsigned head)-1) ->
    s1.(mem) (Int64.repr t) = None \/ s1.(mem) (Int64.repr t) = Some (None)).

(********************)

(**WhileDU1 的语法树定义**)
Module Lang_WhileDU1.
Import Lang_While.
Import Lang_WhileD.

(**在 WhileD 语言的基础上，加入取成员 . 和 -> **)
(**没有（强制）类型转换**)
Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | EAddrOf (e: expr): expr
  | EMember (e: expr) (mem: var_name): expr
  | EPtrMember (e: expr) (mem: var_name): expr.

(**程序语句的语法树中加入局部变量声明， struct/union 成员赋值用 AsgnMember**)
Inductive com : Type :=
  | CSkip: com
  | CLocalVar (t: Types) (x: var_name) (c1: com): com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnMember (e1 e2: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

End Lang_WhileDU1.

(**WhileD+malloc 的语法树定义**)
Module Lang_WhileD_malloc.
Import Lang_While.
Import Lang_WhileD.

(**就是 WhileD 的表达式语法**)
Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | EAddrOf (e: expr): expr.

(**程序语句的语法树中加入局部变量声明（ malloc ）**)
(**malloc 需要传入申请的内存长度 e ，在局部变量声明语句末尾释放**)
Inductive com : Type :=
  | CSkip: com
  | CLocalVarMalloc (x: var_name) (e: expr) (c1: com): com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

End Lang_WhileD_malloc.

Definition is_condtype (t: Types): Prop :=
  match t with
  | Int64 => True
  | Pointer _ => True
  | _ => False
  end.

(********************)

(**WhileDU1 的指称语义**)
Module DntSem_WhileDU1.
Import Lang_While.
Import Lang_WhileD.
Import Lang_WhileDU1.

Module EDenoteDU1.
(**表达式正常求值情况： 程序状态 求值结果类型 求值结果值 的三元关系**)
Record EDenote: Type := {
  nrm: state -> Types -> int64 -> Prop;
  err: state -> Prop;
}.
End EDenoteDU1.

Import EDenoteDU1.

(**定义 WhileDU1 表达式的指称语义**)
(**除表达式树外，还需给出 Struct/Union 定义 SUDef 和外部变量的类型 (var_name->Types) （这里认为外部未定义的变量名不会被使用，该变量名对应的类型任意）**)
(**SUDef -> (var_name->Types) -> EDenote**)

(**由于加入了类型系统，各种运算要求运算数类型合法，不合法定义为求值错误 err ，合法情况和求值结果类型具体如下：**)
(**除特别说明，均与 C 语言相同**)
(**+: int+int=>int , int+ptr(XX)=>ptr(XX) , ptr(XX)+int=>ptr(XX). **)
(**指针与 int 相加的值定义为指针指向地址与 int 的直接相加**)
(**-: int-int=>int , ptr(XX)-int=>ptr(XX) , ptr(XX)-ptr(XX)=>int. **)
(**同类型指针相减的值定义为指针指向地址的直接相减**)
(*** / %: int·int=>int. **)
(**cmp: int·int=>int , ptr(XX)·ptr(XX)=>int. **)
(**neg: -int=>int. **)
(**cond_type := {int | ptr(XX)}**)
(**not: !cond_type=>int. **)
(**and or: cond_type·cond_type=>int. **)

(**不保证定义的 err 语义是正确的. 后续精化关系只需使用表达式的 nrm 语义**)

Notation "x '.(nrm)'" := (EDenoteDU1.nrm x)
  (at level 1, only printing).
Notation "x '.(err)'" := (EDenoteDU1.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenoteDU1.nrm x).
Ltac any_err x := exact (EDenoteDU1.err x).
Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).
Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

(**+ - * **)
Definition arith_compute1_nrm
             (Zfun: Z -> Z -> Z)
             (i1 i2 i: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    i = Int64.repr res /\
    Int64.min_signed <= res <= Int64.max_signed.

Definition arith_compute1_err
             (Zfun: Z -> Z -> Z)
             (i1 i2: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    res < Int64.min_signed \/ res > Int64.max_signed.

Definition add_sem_nrm
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ D2 s t2 i2 /\
    match (t1, t2) with
    | (Int64, Int64) => t=Int64
    | (Int64, Pointer _) => t=t2
    | (Pointer _, Int64) => t=t1
    | _ => False
    end /\
    arith_compute1_nrm Z.add i1 i2 i.

Definition add_sem_err
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ D2 s t2 i2 /\
    (match (t1, t2) with
    | (Int64, Int64) => False
    | (Int64, Pointer _) => False
    | (Pointer _, Int64) => False
    | _ => True
    end \/
    arith_compute1_err Z.add i1 i2).

Definition add_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := add_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           add_sem_err D1.(nrm) D2.(nrm);
  |}.

Definition sub_sem_nrm
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ D2 s t2 i2 /\
    match (t1, t2) with
    | (Int64, Int64) => t=Int64
    | (Pointer _, Int64) => t=t1
    | (Pointer _, Pointer _) => t1=t2 /\ t=Int64
    | _ => False
    end /\
    arith_compute1_nrm Z.sub i1 i2 i.

Definition sub_sem_err
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ D2 s t2 i2 /\
    (match (t1, t2) with
    | (Int64, Int64) => False
    | (Pointer _, Int64) => False
    | (Pointer _, Pointer _) => False
    | _ => True
    end \/
    arith_compute1_err Z.sub i1 i2).

Definition sub_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := sub_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           sub_sem_err D1.(nrm) D2.(nrm);
  |}.

Definition mul_sem_nrm
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ D2 s t2 i2 /\
    match (t1, t2) with
    | (Int64, Int64) => t=Int64
    | _ => False
    end /\
    arith_compute1_nrm Z.mul i1 i2 i.

Definition mul_sem_err
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ D2 s t2 i2 /\
    (match (t1, t2) with
    | (Int64, Int64) => False
    | _ => True
    end \/
    arith_compute1_err Z.mul i1 i2).

Definition mul_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := mul_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           mul_sem_err D1.(nrm) D2.(nrm);
  |}.

(**/ %**)
Definition arith_compute2_nrm
             (int64fun: int64 -> int64 -> int64)
             (i1 i2 i: int64): Prop :=
  i = int64fun i1 i2 /\
  Int64.signed i2 <> 0 /\
  (Int64.signed i1 <> Int64.min_signed \/
   Int64.signed i2 <> - 1).

Definition arith_compute2_err (i1 i2: int64): Prop :=
  Int64.signed i2 = 0 \/
  (Int64.signed i1 = Int64.min_signed /\
   Int64.signed i2 = - 1).
 
Definition arith_sem2_nrm
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists i1 i2,
    D1 s Int64 i1 /\ D2 s Int64 i2 /\
    t=Int64 /\ arith_compute2_nrm int64fun i1 i2 i.

Definition arith_sem2_err
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ D2 s t2 i2 /\
    (t1<>Int64 \/ t2<>Int64 \/ arith_compute2_err i1 i2).

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem2_err D1.(nrm) D2.(nrm);
  |}.

(**cmp**)
Definition cmp_compute_nrm
             (c: comparison)
             (i1 i2 i: int64): Prop :=
  i = if Int64.cmp c i1 i2
      then Int64.repr 1
      else Int64.repr 0.

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ D2 s t2 i2 /\
    match (t1, t2) with
    | (Int64, Int64) => t=Int64
    | (Pointer _, Pointer _) => t1=t2 /\ t=Int64
    | _ => False
    end /\
    cmp_compute_nrm c i1 i2 i.

Definition cmp_sem_err
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ D2 s t2 i2 /\
    match (t1, t2) with
    | (Int64, Int64) => False
    | (Pointer _, Pointer _) => t1<>t2
    | _ => True
    end.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪ cmp_sem_err D1.(nrm) D2.(nrm);
  |}.

(**neg not**)
Definition neg_compute_nrm (i1 i: int64): Prop :=
  i = Int64.neg i1 /\
  Int64.signed i1 <> Int64.min_signed.

Definition neg_compute_err (i1: int64): Prop :=
  Int64.signed i1 = Int64.min_signed.

Definition not_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 0 \/
  i1 = Int64.repr 0 /\ i = Int64.repr 1.

Definition neg_sem_nrm
             (D1: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1, D1 s t1 i1 /\ t1=Int64 /\ t=Int64 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1, D1 s t1 i1 /\ (t1<>Int64 \/ neg_compute_err i1).

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1, D1 s t1 i1 /\ (is_condtype t1) /\ t=Int64 /\ not_compute_nrm i1 i.

Definition not_sem_err
             (D1: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1, D1 s t1 i1 /\ t1<>Int64.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err) ∪ not_sem_err D1.(nrm);
  |}.

(**and or (ShortCut)**)
Definition SC_and_compute_nrm (i1 i: int64): Prop :=
  i1 = Int64.repr 0 /\ i = Int64.repr 0.

Definition SC_or_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 1.

Definition NonSC_and (i1: int64): Prop :=
  Int64.signed i1 <> 0.

Definition NonSC_or (i1: int64): Prop :=
  i1 = Int64.repr 0.

Definition NonSC_compute_nrm (i2 i: int64): Prop :=
  i2 = Int64.repr 0 /\ i = Int64.repr 0 \/
  Int64.signed i2 <> 0 /\ i = Int64.repr 1.
  
Definition and_sem_nrm
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1,
    t=Int64 /\
    D1 s t1 i1 /\
    match t1 with
    | Int64 => True
    | Pointer _ => True
    | _ => False
    end /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists t2 i2,
       D2 s t2 i2 /\
       match t2 with
       | Int64 => True
       | Pointer _ => True
       | _ => False
      end /\ NonSC_compute_nrm i2 i).

Definition and_sem_err1
             (D1: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1,
    D1 s t1 i1 /\
    match t1 with
       | Int64 => False
       | Pointer _ => False
       | _ => True
    end.

Definition and_sem_err2
             (D1: state -> Types -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists t1 i1,
    D1 s t1 i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem_err3
             (D1: state -> Types -> int64 -> Prop)
             (D2: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ NonSC_and i1 /\ D2 s t2 i2 /\
    match t2 with
       | Int64 => False
       | Pointer _ => False
       | _ => True
    end.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err1 D1.(nrm) ∪ 
      and_sem_err2 D1.(nrm) D2.(err) ∪ and_sem_err3 D1.(nrm) D2.(nrm);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1,
    t=Int64 /\
    D1 s t1 i1 /\
    match t1 with
    | Int64 => True
    | Pointer _ => True
    | _ => False
    end /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists t2 i2,
       D2 s t2 i2 /\
       match t2 with
       | Int64 => True
       | Pointer _ => True
       | _ => False
       end /\ NonSC_compute_nrm i2 i).

Definition or_sem_err1
             (D1: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1,
    D1 s t1 i1 /\
    match t1 with
       | Int64 => False
       | Pointer _ => False
       | _ => True
    end.

Definition or_sem_err2
             (D1: state -> Types -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists t1 i1,
    D1 s t1 i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem_err3
             (D1: state -> Types -> int64 -> Prop)
             (D2: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1 t2 i2,
    D1 s t1 i1 /\ NonSC_or i1 /\ D2 s t2 i2 /\
    match t2 with
       | Int64 => False
       | Pointer _ => False
       | _ => True
    end.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err1 D1.(nrm) ∪ 
      or_sem_err2 D1.(nrm) D2.(err) ∪ or_sem_err3 D1.(nrm) D2.(nrm);
  |}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => add_sem D1 D2
  | OMinus => sub_sem D1 D2
  | OMul => mul_sem D1 D2
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s t i =>
             t=Int64 /\ i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

Definition deref_sem_nrm
             (D1: state -> Types -> int64 -> Prop)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1,
    D1 s t1 i1 /\ t1=(Pointer t) /\
    s.(mem) i1 = Some (Some (Vint i)).

Definition deref_sem_err
             (D1: state -> Types -> int64 -> Prop)
             (s: state): Prop :=
  exists t1 i1,
    D1 s t1 i1 /\
    (match t1 with
    | Pointer _ => False
    | _ => True
    end \/
    s.(mem) i1 = None \/ s.(mem) i1 = Some None \/ s.(mem) i1 = Some (Some Vuninit)).

Definition deref_sem_r (D1: EDenote): EDenote :=
  {|
    nrm := deref_sem_nrm D1.(nrm);
    err := D1.(err) ∪ deref_sem_err D1.(nrm);
  |}.

Definition var_sem_l (envt: var_name->Types) (X: var_name): EDenote :=
  {|
    nrm := fun s t i => Pointer (envt X)=t /\ s.(env) X = Some i;
    err := fun s => s.(env) X = None;
  |}.

Definition var_sem_r (envt: var_name->Types) (X: var_name): EDenote :=
  deref_sem_r (var_sem_l envt X).

Fixpoint findfoc (ls:(list Var_Def)) (foc:var_name): (option Types):=
  match ls with
  | nil => None
  | cons vardef cdr =>
      if ((eqb (name vardef) foc)) then (Some (type vardef)) 
        else (findfoc cdr foc)
  end.

(**根据偏移量访问成员**)
Definition member_sem_nrm
             (sudef: SUDef)
             (D1: state -> Types -> int64 -> Prop) (x: var_name)
             (s: state)
             (t: Types) (i: int64): Prop :=
  exists t1 i1 to,
    D1 s t1 i1 /\
    match t1 with
    | Pointer (Struct n) =>
      match ((SDef sudef) n) with
      | Some ls =>
        (findfoc ls x)=(Some to) /\ t=(Pointer to) /\
        ((Int64.min_signed <= (offset (Struct n) x sudef) <= Int64.max_signed)/\
        arith_compute1_nrm Z.add i1 (Int64.repr (offset (Struct n) x sudef)) i)
      | None => False
      end
      (**i1+offset**)
    | Pointer (Union n) =>
      match ((UDef sudef) n) with
      | Some ls =>
        (findfoc ls x)=(Some to) /\ t=(Pointer to) /\
        arith_compute1_nrm Z.add i1 (Int64.repr (offset (Union n) x sudef)) i
      | None => False
      end
    | _ => False
    end.

Definition member_sem_err
             (sudef: SUDef)
             (D1: state -> Types -> int64 -> Prop) (x: var_name)
             (s: state): Prop :=
  exists t1 i1,
    D1 s t1 i1 /\
    match t1 with
    | Pointer (Struct n) =>
      match ((SDef sudef) n) with
      | Some ls =>
        (findfoc ls x)=None \/ (offset (Struct n) x sudef) < Int64.min_signed \/ (offset (Struct n) x sudef) > Int64.max_signed \/ 
        arith_compute1_err Z.add i1 (Int64.repr (offset (Struct n) x sudef))
      | None => True
      end
    | Pointer (Union n) =>
      match ((UDef sudef) n) with
      | Some ls =>
        (findfoc ls x)=None \/
        arith_compute1_err Z.add i1 (Int64.repr (offset (Union n) x sudef))
      | None => True
      end
    | _ => True
    end.

Definition member_sem_l (sudef: SUDef) (D1: EDenote) (x: var_name): EDenote :=
  {|
    nrm := member_sem_nrm sudef D1.(nrm) x;
    err := D1.(err) ∪ member_sem_err sudef D1.(nrm) x;
  |}.

Definition member_sem_r (sudef: SUDef) (D1: EDenote) (x: var_name): EDenote :=
  deref_sem_r (member_sem_l sudef D1 x).

Fixpoint eval_r (sudef: SUDef) (envt: var_name->Types) (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem_r envt X
  | EBinop op e1 e2 =>
      binop_sem op (eval_r sudef envt e1) (eval_r sudef envt e2)
  | EUnop op e1 =>
      unop_sem op (eval_r sudef envt e1)
  | EDeref e1 =>
      deref_sem_r (eval_r sudef envt e1)
  | EAddrOf e1 =>
      eval_l sudef envt e1
  | EMember e1 x =>
      member_sem_r sudef (eval_l sudef envt e1) x
  | EPtrMember e1 x =>
      member_sem_r sudef (eval_r sudef envt e1) x
  end
with eval_l (sudef: SUDef) (envt: var_name->Types) (e: expr): EDenote :=
  match e with
  | EVar X =>
      var_sem_l envt X
  | EDeref e1 =>
      eval_r sudef envt e1
  | EMember e1 x =>
      member_sem_l sudef (eval_l sudef envt e1) x
  | EPtrMember e1 x =>
      member_sem_l sudef (eval_r sudef envt e1) x
  | _ =>
      {| nrm := ∅; err := Sets.full; |}
  end.

(**由于进行程序变换时需要对形如 e.x e->x 的表达式进行变换，变换后显式给出偏移量需要在语法上推断 e 的求值结果类型，故定义计算表达式类型的函数**)

(**查找域中元素类型的函数**)
Definition findfoc_t (sudef: SUDef) (T: Types) (x: var_name): Types :=
      match T with
      | Pointer (Struct n) =>
          match (SDef sudef n) with
          | Some ls =>
              match (findfoc ls x) with
              | Some t => t
              | _ => Int64
              end
          | _ => Int64
          end
      | Pointer (Union n) =>
          match (UDef sudef n) with
          | Some ls =>
              match (findfoc ls x) with
              | Some t => t
              | _ => Int64
              end
          | _ => Int64
          end
      | _ => Int64
      end.

(**定义计算表达式类型的函数**)
(**在不能正常求值时该函数给出的类型可以任意，这对整个证明是足够的**)
(**后续 WhileDU1_DntSemnrm_TypeEq 将证明，给定 SUDef 和变量类型环境，同一表达式在任意程序状态下，正常求值结果的类型一定是以下函数给出的类型**)
Fixpoint type_r (sudef: SUDef) (envt: var_name->Types) (e: expr): Types :=
  match e with
  | EConst n => Int64
  | EVar X => envt X
  | EBinop op e1 e2 =>
      match op with
      | OOr | OAnd => Int64
      | OLt | OLe | OGt | OGe | OEq | ONe => Int64
      | OMul | ODiv | OMod => Int64
      | OPlus =>
          match ((type_r sudef envt e1), (type_r sudef envt e2)) with
          | (Int64, Int64) => Int64
          | (Int64, Pointer _) => (type_r sudef envt e2)
          | (Pointer _, Int64) => (type_r sudef envt e1)
          | _ => Int64
          end
      | OMinus =>
          match ((type_r sudef envt e1), (type_r sudef envt e2)) with
          | (Int64, Int64) => Int64
          | (Pointer _, Int64) => (type_r sudef envt e1)
          | (Pointer _, Pointer _) => Int64
          | _ => Int64
          end
      end
  | EUnop op e1 => Int64
  | EDeref e1 =>
      match (type_r sudef envt e1) with
      | (Pointer t) => t
      | _ => Int64
      end
  | EAddrOf e1 => type_l sudef envt e1
  | EMember e1 x => findfoc_t sudef (type_l sudef envt e1) x
  | EPtrMember e1 x => findfoc_t sudef (type_r sudef envt e1) x
  end
with type_l (sudef: SUDef) (envt: var_name->Types) (e: expr): Types :=
  match e with
  | EVar X => Pointer (envt X)
  | EDeref e1 => (type_r sudef envt e1)
  | EMember e1 x => Pointer (findfoc_t sudef (type_l sudef envt e1) x)
  | EPtrMember e1 x => Pointer (findfoc_t sudef (type_r sudef envt e1) x)
  | _ => Int64
  end.

Module CDenoteDU1.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenoteDU1.

Import CDenoteDU1.

(**定义 WhileDU1 程序的指称语义**)
(**除程序语句树外，同样需给出 Struct/Union 定义 SUDef 和外部变量的类型 (var_name->Types) **)
(**SUDef -> (var_name->Types) -> CDenote**)

Notation "x '.(nrm)'" := (CDenoteDU1.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenoteDU1.err x)
  (at level 1, only printing).

Notation "x '.(inf)'" := (CDenoteDU1.inf x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenoteDU1.nrm x)
  | CDenote => exact (CDenoteDU1.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenoteDU1.err x)
  | CDenote => exact (CDenoteDU1.err x)
  end.

Ltac any_inf x := exact (CDenoteDU1.inf x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).
Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).
Notation "x '.(inf)'" := (ltac:(any_inf x))
  (at level 1, only parsing).

(**test_true test_false**)
(**要求求值结果类型是可以作为条件的类型，即 int 或 ptr(XX) ，这与 C 语言相同；否则定义为 err**)
Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists t i, D.(nrm) s t i /\ Int64.signed i <> 0 /\ is_condtype t).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s => 
      exists t, D.(nrm) s t (Int64.repr 0) /\ is_condtype t).

Definition test_err (D: EDenote):
  state -> Prop :=
  (fun s => exists t i, D.(nrm) s t i /\ not (is_condtype t)).

(**skip seq if while**)
Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪ test_err D0 ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.

Fixpoint boundedLB_nrm
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1.(nrm) ∘ boundedLB_nrm D0 D1 n0) ∪
      (test_false D0)
  end.

Fixpoint boundedLB_err
           (D0: EDenote)
           (D1: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D1.(nrm) ∘ boundedLB_err D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err) ∪ test_err D0
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘ ((D1.(nrm) ∘ X) ∪ D1.(inf)).

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (boundedLB_nrm D0 D1);
    err := ⋃ (boundedLB_err D0 D1);
    inf := Sets.general_union (is_inf D0 D1);
  |}.

(**向地址赋值的指称语义，要求赋值前该地址有访问权限且正在被使用，前后所有变量的地址情况相同，且类型相同且为 int 或 ptr(XX)**)
Definition asgn_deref_sem_nrm
             (D1 D2: state -> Types -> int64 -> Prop)
             (s1 s2: state): Prop :=
  exists t1 i1 t2 i2,
    D1 s1 t1 i1 /\
    D2 s1 t2 i2 /\
    (t1=t2 /\ is_condtype t1) /\
    s1.(mem) i1 <> None /\
    s1.(mem) i1 <> Some (None) /\
    s2.(mem) i1 = Some (Some (Vint i2)) /\
    (forall X, s1.(env) X = s2.(env) X) /\
    (forall p, i1 <> p -> s1.(mem) p = s2.(mem) p).

Definition asgn_deref_sem_err
             (D1 D2: state -> Types -> int64 -> Prop)
             (s1: state): Prop :=
  exists t1 i1 t2 i2,
    D1 s1 t1 i1 /\
    D2 s1 t2 i2 /\
    (t1<>t2 \/ not (is_condtype t1) \/ s1.(mem) i1 = None \/ s1.(mem) i1 = Some (None)).

Definition asgn_deref_sem
             (D1 D2: EDenote): CDenote :=
  {|
    nrm := asgn_deref_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           asgn_deref_sem_err D2.(nrm) D2.(nrm);
    inf := ∅;
  |}.

(**变量赋值的指称语义**)
Definition asgn_var_sem
             (envt: var_name -> Types) (X: var_name)
             (D1: EDenote): CDenote :=
  asgn_deref_sem (var_sem_l envt X) D1.

(**Struct/Union 成员赋值的指称语义**)
(**只能给 int 或 ptr(XX) 赋值，其余定义为 err**)
Definition asgn_member_sem
             (def: SUDef) (envt: var_name -> Types) (e: expr)
             (D1: EDenote): CDenote :=
  match e with
  | EMember e1 x => asgn_deref_sem (eval_l def envt e) D1
  | EPtrMember e1 x => asgn_deref_sem (eval_l def envt e) D1
  | _ => {| nrm:=∅; err:=Sets.full; inf:=∅; |}
  end.

(**局部变量声明的指称语义**)
(**局部变量声明语句申请的内存块大小为类型的大小. 先找到连续的有访问权限且没有被分配的一段内存，执行 malloc_nrm （将该变量地址设为段首地址，整段内存上的每个值变为可分配、被分配、未初始化的值）；如果分配失败（无法分配合法的一段内存），定义为求值错误.**)
(**内部语句执行完释放局部变量时，执行 free_nrm （将该段内存上的每个值置为可分配未被分配的值，将该变量地址改回初始状态）**)
Definition local_sem_nrm
             (X: var_name) (len: Z) (D2: CDenote)
             (s1 s2: state): Prop :=
  (Int64.min_signed <= len <= Int64.max_signed) /\
  exists i2,
    ((malloc_nrm X (Int64.repr len) i2) ∘ D2.(nrm) ∘ (free_nrm X (Int64.repr len) i2 s1)) s1 s2.

Definition local_sem_err
             (X: var_name) (len: Z) (D2: CDenote)
             (s1: state): Prop :=
  (len<Int64.min_signed \/ len>Int64.max_signed) \/
    ((forall i2, malloc_invalid X (Int64.repr len) i2 s1) \/
    (exists i2, ((malloc_nrm X (Int64.repr len) i2) ∘ D2.(err)) s1) \/
    (exists i2, ((malloc_nrm X (Int64.repr len) i2) ∘ D2.(nrm) ∘ (free_invalid X (Int64.repr len) i2)) s1)).

Definition local_sem_inf
             (X: var_name) (len: Z) (D2: CDenote)
             (s1: state): Prop :=
  (Int64.min_signed <= len <= Int64.max_signed) /\
  exists i2, ((malloc_nrm X (Int64.repr len) i2) ∘ D2.(inf)) s1.

Definition local_sem
  (X: var_name) (len: Z) (D2: CDenote) : CDenote :=
  {|
    nrm := local_sem_nrm X len D2;
    err := local_sem_err X len D2;
    inf := local_sem_inf X len D2;
  |}.

Definition new_local (envt: var_name -> Types) (X: var_name) (t: Types)
  (n: var_name): Types :=
  if (eqb n X) then t else envt n.

(**程序语句指称语义**)
(**Print com.**)
Fixpoint eval_com (def: SUDef) (envt: var_name -> Types) (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgnVar X e =>
      asgn_var_sem envt X (eval_r def envt e)
  | CAsgnDeref e1 e2 =>
      asgn_deref_sem (eval_r def envt e1) (eval_r def envt e2)
  | CAsgnMember e1 e2 =>
      asgn_member_sem def envt e1 (eval_r def envt e2)
  | CSeq c1 c2 =>
      seq_sem (eval_com def envt c1) (eval_com def envt c2)
  | CIf e c1 c2 =>
      if_sem (eval_r def envt e) (eval_com def envt c1) (eval_com def envt c2)
  | CWhile e c1 =>
      while_sem (eval_r def envt e) (eval_com def envt c1)
  | CLocalVar t X c =>
      local_sem X (sizeof t def) (eval_com def (new_local envt X t) c)
  end.

End DntSem_WhileDU1.

(********************)

(**WhileD+malloc 的指称语义**)
Module DntSem_WhileD_malloc.
Import Lang_While.
Import Lang_WhileD_malloc.

Module EDenoteDmalloc.
Record EDenote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.
(**表达式的指称语义定义与 WhileD 相同**)
End EDenoteDmalloc.

Import EDenoteDmalloc.
Notation "x '.(nrm)'" := (EDenoteDmalloc.nrm x)
  (at level 1, only printing).
Notation "x '.(err)'" := (EDenoteDmalloc.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenoteDmalloc.nrm x).
Ltac any_err x := exact (EDenoteDmalloc.err x).
Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).
Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

(**+ - * **)
Definition arith_compute1_nrm
             (Zfun: Z -> Z -> Z)
             (i1 i2 i: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    i = Int64.repr res /\
    Int64.min_signed <= res <= Int64.max_signed.

Definition arith_compute1_err
             (Zfun: Z -> Z -> Z)
             (i1 i2: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    res < Int64.min_signed \/ res > Int64.max_signed.

Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.

(**/ %**)
Definition arith_compute2_nrm
             (int64fun: int64 -> int64 -> int64)
             (i1 i2 i: int64): Prop :=
  i = int64fun i1 i2 /\
  Int64.signed i2 <> 0 /\
  (Int64.signed i1 <> Int64.min_signed \/
   Int64.signed i2 <> - 1).

Definition arith_compute2_err (i1 i2: int64): Prop :=
  Int64.signed i2 = 0 \/
  (Int64.signed i1 = Int64.min_signed /\
   Int64.signed i2 = - 1).
 
Definition arith_sem2_nrm
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_nrm int64fun i1 i2 i.

Definition arith_sem2_err
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_err i1 i2.

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem2_err D1.(nrm) D2.(nrm);
  |}.

(**cmp**)
Definition cmp_compute_nrm
             (c: comparison)
             (i1 i2 i: int64): Prop :=
  i = if Int64.cmp c i1 i2
      then Int64.repr 1
      else Int64.repr 0.

Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err);
  |}.

(**neg not**)
Definition neg_compute_nrm (i1 i: int64): Prop :=
  i = Int64.neg i1 /\
  Int64.signed i1 <> Int64.min_signed.

Definition neg_compute_err (i1: int64): Prop :=
  Int64.signed i1 = Int64.min_signed.

Definition not_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 0 \/
  i1 = Int64.repr 0 /\ i = Int64.repr 1.
  
Definition neg_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1, D1 s i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.

(**and or (ShortCut)**)
Definition SC_and_compute_nrm (i1 i: int64): Prop :=
  i1 = Int64.repr 0 /\ i = Int64.repr 0.

Definition SC_or_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 1.

Definition NonSC_and (i1: int64): Prop :=
  Int64.signed i1 <> 0.

Definition NonSC_or (i1: int64): Prop :=
  i1 = Int64.repr 0.

Definition NonSC_compute_nrm (i2 i: int64): Prop :=
  i2 = Int64.repr 0 /\ i = Int64.repr 0 \/
  Int64.signed i2 <> 0 /\ i = Int64.repr 1.
  
Definition and_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition and_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

Definition or_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists i2,
       D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
  |}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2
  | OMinus => arith_sem1 Z.sub D1 D2
  | OMul => arith_sem1 Z.mul D1 D2
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.

Definition deref_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ s.(mem) i1 = Some (Some (Vint i)).

Definition deref_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\
    (s.(mem) i1 = None \/ s.(mem) i1 = Some None \/ s.(mem) i1 = Some (Some Vuninit)).

Definition deref_sem_r (D1: EDenote): EDenote :=
  {|
    nrm := deref_sem_nrm D1.(nrm);
    err := D1.(err) ∪ deref_sem_err D1.(nrm);
  |}.

Definition var_sem_l (X: var_name): EDenote :=
  {|
    nrm := fun s i => s.(env) X = Some i;
    err := fun s => s.(env) X = None;
  |}.

Definition var_sem_r (X: var_name): EDenote :=
  deref_sem_r (var_sem_l X).

Fixpoint eval_r (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem_r X
  | EBinop op e1 e2 =>
      binop_sem op (eval_r e1) (eval_r e2)
  | EUnop op e1 =>
      unop_sem op (eval_r e1)
  | EDeref e1 =>
      deref_sem_r (eval_r e1)
  | EAddrOf e1 =>
      eval_l e1
  end
with eval_l (e: expr): EDenote :=
  match e with
  | EVar X =>
      var_sem_l X
  | EDeref e1 =>
      eval_r e1
  | _ =>
      {| nrm := ∅; err := Sets.full; |}
  end.

(**test_true test_false**)
Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (Int64.repr 0)).

(**WhileD+malloc 程序语句的指称语义**)
Module CDenoteDmalloc.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenoteDmalloc.

Import CDenoteDmalloc.

Notation "x '.(nrm)'" := (CDenoteDmalloc.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenoteDmalloc.err x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenoteDmalloc.nrm x)
  | CDenote => exact (CDenoteDmalloc.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenoteDmalloc.err x)
  | CDenote => exact (CDenoteDmalloc.err x)
  end.

(**skip seq if while 的指称语义**)
Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.

Fixpoint boundedLB_nrm
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1.(nrm) ∘ boundedLB_nrm D0 D1 n0) ∪
      (test_false D0)
  end.

Fixpoint boundedLB_err
           (D0: EDenote)
           (D1: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D1.(nrm) ∘ boundedLB_err D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘ ((D1.(nrm) ∘ X) ∪ D1.(inf)).

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (boundedLB_nrm D0 D1);
    err := ⋃ (boundedLB_err D0 D1);
    inf := Sets.general_union (is_inf D0 D1);
  |}.

(**向地址赋值的指称语义，要求赋值前该地址有访问权限且正在被使用，前后所有变量的地址情况相同**)
Definition asgn_deref_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s1 s2: state): Prop :=
  exists i1 i2,
    D1 s1 i1 /\
    D2 s1 i2 /\
    s1.(mem) i1 <> None /\
    s1.(mem) i1 <> Some (None) /\
    s2.(mem) i1 = Some (Some (Vint i2)) /\
    (forall X, s1.(env) X = s2.(env) X) /\
    (forall p, i1 <> p -> s1.(mem) p = s2.(mem) p).

Definition asgn_deref_sem_err
             (D1: state -> int64 -> Prop)
             (s1: state): Prop :=
  exists i1,
    D1 s1 i1 /\
    (s1.(mem) i1 = None \/
    s1.(mem) i1 = Some (None)).

Definition asgn_deref_sem
             (D1 D2: EDenote): CDenote :=
  {|
    nrm := asgn_deref_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           asgn_deref_sem_err D2.(nrm);
    inf := ∅;
  |}.

(**变量赋值的指称语义**)
Definition asgn_var_sem
             (X: var_name)
             (D1: EDenote): CDenote :=
  asgn_deref_sem (var_sem_l X) D1.

(**局部变量声明的指称语义**)
(**局部变量声明语句给出申请的内存块大小. 先找到连续的可分配且没有被分配的一段内存，执行 malloc_nrm （将该变量地址设为段首地址，整段内存上的每个值变为可分配、被分配、未初始化的值）；如果分配失败，定义为求值错误.**)
(**内部语句执行完释放局部变量时，执行 free_nrm （将该段内存上的每个值置为有访问权限未被分配的值，将该变量地址改回初始状态）**)
Definition local_sem_nrm
             (X: var_name) (D1: state -> int64 -> Prop) (D2: CDenote)
             (s1 s2: state): Prop :=
  exists i1 i2,
    D1 s1 i1 /\
    ((malloc_nrm X i1 i2) ∘ D2.(nrm) ∘ (free_nrm X i1 i2 s1)) s1 s2.

Definition local_sem_err
             (X: var_name) (D1: state -> int64 -> Prop) (D2: CDenote)
             (s1: state): Prop :=
  exists i1, D1 s1 i1 /\
    ((forall i2, malloc_invalid X i1 i2 s1) \/
    (exists i2, ((malloc_nrm X i1 i2) ∘ D2.(err)) s1) \/
    (exists i2, ((malloc_nrm X i1 i2) ∘ D2.(nrm) ∘ (free_invalid X i1 i2)) s1)).

Definition local_sem_inf
             (X: var_name) (D1: state -> int64 -> Prop) (D2: CDenote)
             (s1: state): Prop :=
  exists i1, D1 s1 i1 /\
    (exists i2, ((malloc_nrm X i1 i2) ∘ D2.(inf)) s1).

Definition local_sem
  (X: var_name) (D1: EDenote) (D2: CDenote) : CDenote :=
  {|
    nrm := local_sem_nrm X D1.(nrm) D2;
    err := D1.(err) ∪ local_sem_err X D1.(nrm) D2;
    inf := local_sem_inf X D1.(nrm) D2;
  |}.

(**程序语句指称语义**)
Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgnVar X e =>
      asgn_var_sem X (eval_r e)
  | CAsgnDeref e1 e2 =>
      asgn_deref_sem (eval_r e1) (eval_r e2)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_r e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_r e) (eval_com c1)
  | CLocalVarMalloc X e c =>
      local_sem X (eval_r e) (eval_com c)
  end.

End DntSem_WhileD_malloc.

Module RefineRel.
Import Lang_While.
Import Lang_WhileDU1.
Import DntSem_WhileDU1.
(**省略 Lang_WhileDU1. 前缀**)
(**Print Lang_WhileDU1.expr.
Print Lang_WhileD_malloc.expr.
Print EDenoteDU1.
Print DntSem_WhileD_malloc.EDenoteDmalloc.
Print DntSem_WhileDU1.eval_l.
Print DntSem_WhileDU1.eval_r.
Print DntSem_WhileD_malloc.eval_l.
Print DntSem_WhileD_malloc.eval_r.**)

Notation "x '.(mnrm)'" := (DntSem_WhileD_malloc.EDenoteDmalloc.nrm x)
  (at level 1, only printing).
Notation "x '.(merr)'" := (DntSem_WhileD_malloc.EDenoteDmalloc.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (DntSem_WhileD_malloc.EDenoteDmalloc.nrm x).
Ltac any_err x := exact (DntSem_WhileD_malloc.EDenoteDmalloc.err x).
Notation "x '.(mnrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).
Notation "x '.(merr)'" := (ltac:(any_err x))
  (at level 1, only parsing).

(**表达式的精化关系，要求解释为左值和右值时前者均是后者子集**)
Definition ERefineRel (sudef: SUDef) (envt: var_name -> Types) (e1: Lang_WhileDU1.expr) (e2: Lang_WhileD_malloc.expr): Prop :=
  forall s t i,
    ((DntSem_WhileDU1.eval_l sudef envt e1).(nrm) s t i ->
    (DntSem_WhileD_malloc.eval_l e2).(mnrm) s i) /\
    ((DntSem_WhileDU1.eval_r sudef envt e1).(nrm) s t i ->
    (DntSem_WhileD_malloc.eval_r e2).(mnrm) s i).

(**证明表达式中对应的结构保持精化关系**)

Lemma EConst_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types) (n:Z),
  ERefineRel sudef envt (EConst n) (Lang_WhileD_malloc.EConst n).
Proof.
unfold ERefineRel.
intros. simpl.
tauto.
Qed.

Lemma EVar_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types) (x: var_name),
  ERefineRel sudef envt (EVar x) (Lang_WhileD_malloc.EVar x).
Proof.
unfold ERefineRel.
intros. simpl.
split.
+ tauto.
+ intros.
  unfold deref_sem_nrm in H.
  destruct H. destruct H.
  unfold DntSem_WhileD_malloc.deref_sem_nrm.
  exists x1.
  tauto.
Qed.

(***Binop***)
(**+ ; - ; * ; / % ; cmp ; and or ，分类讨论**)

Lemma EBinop_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types) (op: binop)
  (e1 e2: expr) (me1 me2: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e1 me1 ->
  ERefineRel sudef envt e2 me2 ->
  ERefineRel sudef envt (EBinop op e1 e2) (Lang_WhileD_malloc.EBinop op me1 me2).
Proof.
intros.
unfold ERefineRel.
intros.
split;simpl.
+ intros.
  unfold eval_l in H1.
  unfold DntSem_WhileD_malloc.eval_l.
  tauto.
+ intros. 
  destruct op;
  unfold binop_sem in H1;
  unfold DntSem_WhileD_malloc.or_sem_nrm;
  simpl.
  - unfold or_sem in H1.
    simpl in H1.
    unfold or_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.or_sem_nrm.
    unfold DntSem_WhileD_malloc.SC_or_compute_nrm.
    unfold DntSem_WhileD_malloc.NonSC_or.
    unfold DntSem_WhileD_malloc.NonSC_compute_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [_ [? [_ [? | ?] ] ] ] ] ].
    {
        unfold SC_or_compute_nrm in H2.
        exists i1.
        split.
        * apply (H s t1 i1). tauto.
        * left. tauto.
    }
    {
        unfold NonSC_or, NonSC_compute_nrm in H2.
        destruct H2 as [? [t2 [i2 [? [_ ?] ] ] ] ].
        exists i1.
        split.
        * apply (H s t1 i1). tauto.
        * right.
          split.
          ++ tauto.
          ++ exists i2.
             split.
             -- apply (H0 s t2 i2). tauto.
             -- tauto.
    }
  - unfold and_sem in H1.
    simpl in H1.
    unfold and_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.and_sem_nrm.
    unfold DntSem_WhileD_malloc.SC_and_compute_nrm.
    unfold DntSem_WhileD_malloc.NonSC_and.
    unfold DntSem_WhileD_malloc.NonSC_compute_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [_ [? [_ [? | ?] ] ] ] ] ].
    {
        unfold SC_and_compute_nrm in H2.
        exists i1.
        split.
        * apply (H s t1 i1). tauto.
        * left. tauto.
    }
    {
        unfold NonSC_and, NonSC_compute_nrm in H2.
        destruct H2 as [? [t2 [i2 [? [_ ?] ] ] ] ].
        exists i1.
        split.
        * apply (H s t1 i1). tauto.
        * right.
            split.
            ++ tauto.
            ++ exists i2.
            split.
            -- apply (H0 s t2 i2). tauto.
            -- tauto.
    }
  - unfold cmp_sem in H1.
    simpl in H1.
    unfold cmp_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.cmp_sem_nrm.
    unfold DntSem_WhileD_malloc.cmp_compute_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [t2 [i2 [? [? [_ ?] ] ] ] ] ] ].
    unfold cmp_compute_nrm in H3.
    exists i1,i2.
    split.
    * apply (H s t1 i1). tauto.
    * split.
      ++ apply (H0 s t2 i2). tauto.
      ++ tauto.
      - unfold cmp_sem in H1.
      simpl in H1.
      unfold cmp_sem_nrm in H1.
      unfold DntSem_WhileD_malloc.cmp_sem_nrm.
      unfold DntSem_WhileD_malloc.cmp_compute_nrm.
      unfold ERefineRel in H,H0.
      destruct H1 as [t1 [i1 [t2 [i2 [? [? [_ ?] ] ] ] ] ] ].
      unfold cmp_compute_nrm in H3.
      exists i1,i2.
      split.
      * apply (H s t1 i1). tauto.
      * split.
        ++ apply (H0 s t2 i2). tauto.
        ++ tauto.
  - unfold cmp_sem in H1.
    simpl in H1.
    unfold cmp_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.cmp_sem_nrm.
    unfold DntSem_WhileD_malloc.cmp_compute_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [t2 [i2 [? [? [_ ?] ] ] ] ] ] ].
    unfold cmp_compute_nrm in H3.
    exists i1,i2.
    split.
    * apply (H s t1 i1). tauto.
    * split.
      ++ apply (H0 s t2 i2). tauto.
      ++ tauto.
  - unfold cmp_sem in H1.
    simpl in H1.
    unfold cmp_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.cmp_sem_nrm.
    unfold DntSem_WhileD_malloc.cmp_compute_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [t2 [i2 [? [? [_ ?] ] ] ] ] ] ].
    unfold cmp_compute_nrm in H3.
    exists i1,i2.
    split.
    * apply (H s t1 i1). tauto.
    * split.
        ++ apply (H0 s t2 i2). tauto.
        ++ tauto.
  - unfold cmp_sem in H1.
    simpl in H1.
    unfold cmp_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.cmp_sem_nrm.
    unfold DntSem_WhileD_malloc.cmp_compute_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [t2 [i2 [? [? [_ ?] ] ] ] ] ] ].
    unfold cmp_compute_nrm in H3.
    exists i1,i2.
    split.
    * apply (H s t1 i1). tauto.
    * split.
        ++ apply (H0 s t2 i2). tauto.
        ++ tauto.
  - unfold cmp_sem in H1.
    simpl in H1.
    unfold cmp_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.cmp_sem_nrm.
    unfold DntSem_WhileD_malloc.cmp_compute_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [t2 [i2 [? [? [_ ?] ] ] ] ] ] ].
    unfold cmp_compute_nrm in H3.
    exists i1,i2.
    split.
    * apply (H s t1 i1). tauto.
    * split.
        ++ apply (H0 s t2 i2). tauto.
        ++ tauto.
  - unfold add_sem in H1.
    simpl in H1.
    unfold add_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.arith_compute1_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [t2 [i2 [? [? [_ ?] ] ] ] ] ] ].
    exists i1,i2.
    split.
    * apply (H s t1 i1). tauto.
    * split.
        ++ apply (H0 s t2 i2). tauto.
        ++ tauto.
  - unfold sub_sem in H1.
    simpl in H1.
    unfold sub_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.arith_compute1_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [t2 [i2 [? [? [_ ?] ] ] ] ] ] ].
    exists i1,i2.
    split.
    * apply (H s t1 i1). tauto.
    * split.
        ++ apply (H0 s t2 i2). tauto.
        ++ tauto.
  - unfold mul_sem in H1.
    simpl in H1.
    unfold mul_sem_nrm in H1.
    unfold DntSem_WhileD_malloc.arith_compute1_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [t1 [i1 [t2 [i2 [? [? [_ ?] ] ] ] ] ] ].
    exists i1,i2.
    split.
    * apply (H s t1 i1). tauto.
    * split.
        ++ apply (H0 s t2 i2). tauto.
        ++ tauto.
  - unfold arith_sem2 in H1.
    simpl in H1.
    unfold arith_sem2_nrm in H1.
    unfold arith_compute2_nrm in H1.
    unfold DntSem_WhileD_malloc.arith_sem2_nrm.
    unfold DntSem_WhileD_malloc.arith_compute2_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [i1 [i2 [? [? [_ [? ?] ] ] ] ] ].
    exists i1,i2.
    split.
    * apply (H s Int64 i1). tauto.
    * split.
        ++ apply (H0 s Int64 i2). tauto.
        ++ tauto.
  - unfold arith_sem2 in H1.
    simpl in H1.
    unfold arith_sem2_nrm in H1.
    unfold arith_compute2_nrm in H1.
    unfold DntSem_WhileD_malloc.arith_sem2_nrm.
    unfold DntSem_WhileD_malloc.arith_compute2_nrm.
    unfold ERefineRel in H,H0.
    destruct H1 as [i1 [i2 [? [? [_ [? ?] ] ] ] ] ].
    exists i1,i2.
    split.
    * apply (H s Int64 i1). tauto.
    * split.
        ++ apply (H0 s Int64 i2). tauto.
        ++ tauto.
Qed.

(***Unop***)
Lemma EUnop_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types) (op: unop)
  (e: expr) (me: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e me ->
  ERefineRel sudef envt (EUnop op e) (Lang_WhileD_malloc.EUnop op me).
Proof.
intros.
unfold ERefineRel.
unfold ERefineRel in H.
intros.
split;simpl.
+ tauto.
+ intros.
  destruct op; simpl.
  - unfold unop_sem in H0.
    simpl in H0.
    unfold not_sem_nrm in H0.
    destruct H0 as [t1 [i1 [? [_ [_ ?] ] ] ] ].
    unfold not_compute_nrm in H1.
    unfold DntSem_WhileD_malloc.not_sem_nrm.
    unfold DntSem_WhileD_malloc.not_compute_nrm.
    exists i1.
    split.
    * apply (H s t1 i1). tauto.
    * tauto.
  - unfold unop_sem in H0.
    simpl in H0.
    unfold neg_sem_nrm in H0.
    destruct H0 as [t1 [i1 [? [_ [_ ?] ] ] ] ].
    unfold neg_compute_nrm in H1.
    unfold DntSem_WhileD_malloc.neg_sem_nrm.
    unfold DntSem_WhileD_malloc.neg_compute_nrm.
    exists i1.
    split.
    * apply (H s t1 i1). tauto.
    * tauto.
Qed.

Lemma EDeref_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e: expr) (me: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e me ->
  ERefineRel sudef envt (EDeref e) (Lang_WhileD_malloc.EDeref me).
Proof.
intros.
unfold ERefineRel in H.
unfold ERefineRel.
intros.
split;simpl;intros.
+ apply (H s t i). tauto.
+ unfold deref_sem_nrm in H0.
  simpl.
  unfold DntSem_WhileD_malloc.deref_sem_nrm.
  destruct H0 as [t1 [i1 [? [_ ?] ] ] ].
  exists i1.
  split.
  - apply (H s t1 i1). tauto.
  - tauto.
Qed.

Lemma EAddrOf_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e: expr) (me: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e me ->
  ERefineRel sudef envt (EAddrOf e) (Lang_WhileD_malloc.EAddrOf me).
Proof.
intros.
unfold ERefineRel in H.
unfold ERefineRel.
intros.
split;simpl;intros.
+ tauto.
+ apply (H s t i). tauto.
Qed.

(**证明表达式的变换服从精化关系**)
(**Print type_l.
Print expr.
Print eval_l.
Print eval_r.
Print state.
Print Some.**)
(**先证明：给定 SUDef 和变量类型环境，同一表达式在任意程序状态下，正常求值结果的类型总是相同的，即 type_l type_r 从语法上推断出的类型**)
(**结构归纳**)
Lemma WhileDU1_DntSemnrm_TypeEq:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e: expr) (s: state) (t: Types) (i: int64),
  ((eval_l sudef envt e).(nrm) s t i -> t=(type_l sudef envt e)) /\
  ((eval_r sudef envt e).(nrm) s t i -> t=(type_r sudef envt e)).
Proof.
induction e; intros; simpl.
+ split.
  - intros. tauto.
  - tauto.
+ split.
  - intros. destruct H. rewrite H. reflexivity.
  - intros. unfold deref_sem_nrm in H.
    destruct H as [? [? [ [? _] [? _] ] ] ].
    rewrite H0 in H.
    injection H.
    intros. rewrite H1. reflexivity.
+ split.
  - intros. tauto.
  - intros.
    destruct op; simpl in H; simpl.
    * unfold or_sem_nrm in H.
      destruct H as [t1 [i1 [? _] ] ].
      apply H.
    * unfold and_sem_nrm in H.
      destruct H as [t1 [i1 [? _] ] ].
      apply H.
    * unfold cmp_sem_nrm in H.
      destruct H as [t1 [i1 [t2 [i2 [? [? [? _] ] ] ] ] ] ].
      destruct t1;destruct t2; tauto.
    * unfold cmp_sem_nrm in H.
      destruct H as [t1 [i1 [t2 [i2 [? [? [? _] ] ] ] ] ] ].
      destruct t1;destruct t2; tauto.
    * unfold cmp_sem_nrm in H.
      destruct H as [t1 [i1 [t2 [i2 [? [? [? _] ] ] ] ] ] ].
      destruct t1;destruct t2; tauto.
    * unfold cmp_sem_nrm in H.
      destruct H as [t1 [i1 [t2 [i2 [? [? [? _] ] ] ] ] ] ].
      destruct t1;destruct t2; tauto.
    * unfold cmp_sem_nrm in H.
      destruct H as [t1 [i1 [t2 [i2 [? [? [? _] ] ] ] ] ] ].
      destruct t1;destruct t2; tauto.
    * unfold cmp_sem_nrm in H.
      destruct H as [t1 [i1 [t2 [i2 [? [? [? _] ] ] ] ] ] ].
      destruct t1;destruct t2; tauto.
    * unfold add_sem_nrm in H.
      destruct H as [t1 [i1 [t2 [i2 [? [? [? _] ] ] ] ] ] ].
      specialize (IHe1 s t1 i1).
      destruct IHe1 as [_ ?].
      specialize (IHe2 s t2 i2).
      destruct IHe2 as [_ ?].
      apply H2 in H.
      apply H3 in H0.
      rewrite <- H, <- H0.
      destruct t1,t2; simpl; simpl in H1; tauto.
    * unfold sub_sem_nrm in H.
      destruct H as [t1 [i1 [t2 [i2 [? [? [? _] ] ] ] ] ] ].
      specialize (IHe1 s t1 i1).
      destruct IHe1 as [_ ?].
      specialize (IHe2 s t2 i2).
      destruct IHe2 as [_ ?].
      apply H2 in H.
      apply H3 in H0.
      rewrite <- H, <- H0.
      destruct t1,t2; simpl; simpl in H1; tauto.
    * unfold sub_sem_nrm in H.
      destruct H as [t1 [i1 [t2 [i2 [? [? [? _] ] ] ] ] ] ].
      specialize (IHe1 s t1 i1).
      destruct IHe1 as [_ ?].
      specialize (IHe2 s t2 i2).
      destruct IHe2 as [_ ?].
      apply H2 in H.
      apply H3 in H0.
      destruct t1,t2; simpl; simpl in H1; tauto.
    * unfold arith_sem2_nrm in H.
      destruct H as [i1 [i2 [_ [_ [? _] ] ] ] ].
      apply H.
    * unfold arith_sem2_nrm in H.
      destruct H as [i1 [i2 [_ [_ [? _] ] ] ] ].
      apply H.
+ split.
  - intros. tauto.
  - intros.
    destruct op; simpl in H.
    * unfold not_sem_nrm in H.
      destruct H as [t1 [i1 ?] ].
      tauto.
    * unfold neg_sem_nrm in H.
      destruct H as [t1 [i1 ?] ].
      tauto.
+ split.
  - apply (IHe s t i).
  - intros.
    unfold deref_sem_nrm in H.
    destruct H as [t1 [i1 [? [? _] ] ] ].
    apply (IHe s t1 i1) in H.
    rewrite <- H, H0.
    tauto.
+ split.
  - intros. tauto.
  - apply (IHe s t i).
+ split.
  - intros.
    unfold member_sem_nrm in H.
    destruct H as [t1 [i1 [to [? ?] ] ] ]. 
    apply (IHe s t1 i1) in H.
    destruct e; simpl in H; rewrite H in H0;simpl in H0;simpl; try tauto.
    * destruct (envt x); simpl in H0; simpl;try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0);
      simpl in H0; simpl; try tauto;
      destruct H0 as [? [? _] ];
      rewrite H0; tauto.
    * destruct (type_r sudef envt e); simpl in H0; simpl; try tauto.
      destruct t0; simpl in H0; simpl; try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0);
      simpl in H0; simpl; try tauto;
      destruct H0 as [? [? _] ];
      rewrite H0; tauto.
    * destruct (findfoc_t sudef (type_l sudef envt e) mem1); simpl in H0;simpl; try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0);
      simpl in H0; simpl; try tauto;
      destruct H0 as [? [? _] ];
      rewrite H0; tauto.
    * destruct (findfoc_t sudef (type_r sudef envt e) mem1); simpl in H0;simpl; try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0);
      simpl in H0; simpl; try tauto;
      destruct H0 as [? [? _] ];
      rewrite H0; tauto.
  - intros.
    unfold deref_sem_nrm in H.
    destruct H as [t1 [i1 [? [? _] ] ] ].
    unfold member_sem_nrm in H.
    destruct H as [t2 [i2 [to [? ?] ] ] ].
    apply (IHe s t2 i2) in H.
    rewrite H in H1.
    destruct (type_l sudef envt e); simpl in H; simpl; try tauto.
    destruct t0; simpl in H; simpl; try tauto;
    try destruct (SDef sudef name0); try destruct (UDef sudef name0); try tauto;
    destruct H1 as [? [? _] ];
    rewrite H1;
    rewrite H2 in H0;
    injection H0;
    intros; rewrite H3; reflexivity. 
+ split.
  - intros. 
    unfold member_sem_nrm in H.
    destruct H as [t1 [i1 [to [? ?] ] ] ]. 
    apply (IHe s t1 i1) in H.
    destruct e; simpl in H; rewrite H in H0;simpl in H0;simpl; try tauto.
    * destruct (envt x); simpl in H0; simpl; try tauto.
      destruct t0; simpl in H0; simpl; try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0);
      simpl in H0; simpl; try tauto;
      destruct H0 as [? [? _] ];
      rewrite H0; tauto.
    * destruct op; simpl in H0; simpl; try tauto;
      destruct (type_r sudef envt e1); simpl in H0; simpl; try tauto;
      destruct (type_r sudef envt e2); simpl in H0; simpl; try tauto;
      destruct t0; simpl in H0; simpl; try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0);
      simpl in H0; simpl; try tauto;
      destruct H0 as [? [? _] ];
      rewrite H0; tauto.
    * destruct (type_r sudef envt e); simpl in H0; simpl; try tauto.
      destruct t0; simpl in H0; simpl; try tauto.
      destruct t0; simpl in H0; simpl; try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0);
      simpl in H0; simpl; try tauto;
      destruct H0 as [? [? _] ];
      rewrite H0; tauto.
    * destruct (type_l sudef envt e); simpl in H0; simpl; try tauto.
      destruct t0; simpl in H0; simpl; try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0);
      simpl in H0; simpl; try tauto;
      destruct H0 as [? [? _] ];
      rewrite H0; tauto.
    * destruct (type_l sudef envt e); simpl in H0; simpl; try tauto;
      destruct t0; simpl in H0; simpl; try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0);
      simpl in H0; simpl; try tauto;
      try destruct (findfoc l mem1); simpl in H0; simpl; try tauto.
      ++ destruct t0; simpl in H0; simpl; try tauto;
         destruct t0; simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name0); try destruct (UDef sudef name0);
         simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1);
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
      ++ destruct t0; simpl in H0; simpl; try tauto;
         destruct t0; simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name0); try destruct (UDef sudef name0);
         simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1);
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
      ++ destruct (findfoc l0 mem1); simpl in H0; simpl; try tauto.
         destruct t2; simpl in H0; simpl; try tauto.
         destruct t2; simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name0); try destruct (UDef sudef name0);
         simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1);
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
      ++ destruct (findfoc l0 mem1); simpl in H0; simpl; try tauto.
         destruct t0; simpl in H0; simpl; try tauto.
         destruct t0; simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name0); try destruct (UDef sudef name0);
         simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1);
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
      ++ destruct t0; simpl in H0; simpl; try tauto;
         destruct t0; simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name0); try destruct (UDef sudef name0);
         simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1);
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
    * destruct (type_r sudef envt e); simpl in H0; simpl in H; simpl; try tauto.
      destruct t0; simpl in H0; simpl in H; try tauto;
      try destruct (SDef sudef name0); try destruct (UDef sudef name0); 
      simpl in H; simpl in H0; simpl; try tauto;
      try destruct (findfoc l mem1);simpl in H; simpl in H0; simpl; try tauto.
      ++ destruct t0; simpl in H0;simpl;try tauto.
         destruct t0; simpl in H0;simpl;try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1); 
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
      ++ destruct t0; simpl in H0;simpl;try tauto.
         destruct t0; simpl in H0;simpl;try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1); 
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
      ++ destruct (findfoc l0 mem1); simpl in H0; simpl; try tauto;
         destruct t2; simpl in H0; simpl; try tauto;
         destruct t2; simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name0); try destruct (UDef sudef name0);
         simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1);
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
      ++ destruct (findfoc l0 mem1); simpl in H0; simpl; try tauto.
         destruct t0; simpl in H0; simpl; try tauto.
         destruct t0; simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name0); try destruct (UDef sudef name0);
         simpl in H0; simpl; try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1);
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
      ++ destruct t0; simpl in H0;simpl;try tauto.
         destruct t0; simpl in H0;simpl;try tauto;
         try destruct (SDef sudef name1); try destruct (UDef sudef name1); 
         simpl in H0; simpl; try tauto;
         destruct H0 as [? [? _] ];
         rewrite H0; tauto.
  - intros.
    unfold deref_sem_nrm in H.
    destruct H as [t1 [i1 [? [? _] ] ] ].
    unfold member_sem_nrm in H.
    destruct H as [t2 [i2 [to [? ?] ] ] ].
    apply (IHe s t2 i2) in H.
    rewrite <- H.
    destruct e; simpl in H; simpl; try tauto;
    destruct t2; simpl in H;simpl; try tauto;
    destruct t2; simpl in H;simpl; try tauto;
    try destruct (SDef sudef name0); try destruct (UDef sudef name0); 
    simpl in H; simpl;try tauto;
    destruct H1 as [? [? _] ];
    rewrite H1; try tauto;
    rewrite H2 in H0;
    injection H0;
    intros;rewrite H3;reflexivity.
Qed.

Definition offset_p (sudef: SUDef) (t: Types) (x: var_name): Z :=
  match t with
  | Pointer to => (offset to x sudef)
  | _ => 0
  end. 

(**定义表达式的变换**)
(**WhileDU1 中的结构体变量变为分配内存长度为 sizeof Type 的局部变量，其地址为首地址，可做如下变换**)
Fixpoint ETransform
  (sudef: SUDef) (envt: var_name -> Types)
  (e: expr): Lang_WhileD_malloc.expr:=
  match e with
  | EConst n => Lang_WhileD_malloc.EConst n
  | EVar x => Lang_WhileD_malloc.EVar x
  | EBinop op e1 e2 =>
      Lang_WhileD_malloc.EBinop op (ETransform sudef envt e1) (ETransform sudef envt e2)
  | EUnop op e =>
      Lang_WhileD_malloc.EUnop op (ETransform sudef envt e)
  | EDeref e => Lang_WhileD_malloc.EDeref (ETransform sudef envt e)
  | EAddrOf e => Lang_WhileD_malloc.EAddrOf (ETransform sudef envt e)
  (**e.x ==> *(&e+offset) ，计算 offset 需要 e 的类型**)
  | EMember e x =>
      Lang_WhileD_malloc.EDeref (
        Lang_WhileD_malloc.EBinop OPlus
          (Lang_WhileD_malloc.EAddrOf (ETransform sudef envt e))
          (Lang_WhileD_malloc.EConst (offset_p sudef (type_l sudef envt e) x)))
  (**e->x ==> *(e+offset) ，计算 offset 需要 e 的类型**)
  | EPtrMember e x =>
      Lang_WhileD_malloc.EDeref (
        Lang_WhileD_malloc.EBinop OPlus
          (ETransform sudef envt e)
          (Lang_WhileD_malloc.EConst (offset_p sudef (type_r sudef envt e) x)))
  end.

(**证明表达式的变换服从精化关系**)
(**对 e 结构归纳，除 EMember, EPtrMember 外都没有改变结构，直接使用之前的引理**)
Theorem ETransform_RefineRel:
forall (sudef: SUDef) (envt: var_name -> Types) (e: expr),
  ERefineRel sudef envt e (ETransform sudef envt e).
Proof.
  pose proof WhileDU1_DntSemnrm_TypeEq as L.
  induction e;intros;simpl.
  + apply EConst_persistRR.
  + apply EVar_persistRR.
  + apply EBinop_persistRR; tauto.
  + apply EUnop_persistRR. tauto.
  + apply EDeref_persistRR. tauto.
  + apply EAddrOf_persistRR. tauto.
  + unfold ERefineRel in IHe. unfold ERefineRel.
    intros.
    split; simpl; try tauto.
    - intros.
      unfold member_sem_nrm,arith_compute1_nrm in H.
      unfold DntSem_WhileD_malloc.arith_sem1_nrm.
      unfold DntSem_WhileD_malloc.arith_compute1_nrm.
      destruct H as [t1 [i1 [to [? ?] ] ] ].
      destruct t1; simpl in H0;try tauto;
      destruct t1; simpl in H0; try tauto.
      unfold offset_p; simpl;
      simpl;try tauto.
      ++ apply (L sudef envt e s (Pointer (Struct name0)) i1) in H as ?.
         rewrite <- H1.
         unfold offset.
         destruct (SDef sudef name0);simpl.
         -- exists i1, (Int64.repr (calc_offset l mem0 (size sudef))).
            split. apply (IHe s (Pointer (Struct name0)) i1). tauto.
            split; tauto.
         -- tauto.
      ++ apply (L sudef envt e s (Pointer (Union name0)) i1) in H as ?. 
         rewrite <- H1.
         unfold offset.
         destruct (UDef sudef name0);simpl.
         -- exists i1, (Int64.repr 0).
            split. apply (IHe s (Pointer (Union name0)) i1). tauto.
            split. split. tauto. apply (Int64.signed_range (Int64.repr 0)).
            tauto.
         -- tauto.
    - intros.
      unfold member_sem_nrm,arith_compute1_nrm,deref_sem_nrm in H.
      unfold DntSem_WhileD_malloc.arith_sem1_nrm.
      unfold DntSem_WhileD_malloc.arith_compute1_nrm.
      unfold DntSem_WhileD_malloc.deref_sem_nrm.
      destruct H as [t1 [i1 [ [t2 [i2 [to [? ?] ] ] ] [_ ?] ] ] ];
      destruct t2; simpl in H0; try tauto;
      destruct t2; simpl in H0; try tauto;
      unfold offset_p; simpl;
      simpl;try tauto.
      ++ apply (L sudef envt e s (Pointer (Struct name0)) i2) in H as ?.
         rewrite <- H2.
         unfold offset.
         destruct (SDef sudef name0);simpl.
         -- exists i1.
            split. 
            {
                exists i2,(Int64.repr (calc_offset l mem0 (size sudef))).
                split. apply (IHe s(Pointer (Struct name0)) i2). tauto.
                tauto.
            }
            tauto.
         -- exists i1.
            split.
            {
                exists i2, (Int64.repr 0).
                split. apply (IHe s (Pointer (Union name0)) i2). tauto.
                split. split. tauto. apply (Int64.signed_range (Int64.repr 0)).
                tauto.
            }
            tauto.
      ++ apply (L sudef envt e s (Pointer (Union name0)) i2) in H as ?.
         rewrite <- H2.
         unfold offset.
         destruct (UDef sudef name0);simpl.
         -- exists i1.
            split. 
            {
                exists i2, (Int64.repr 0).
                split. apply (IHe s (Pointer (Union name0)) i2). tauto.
                split. split. tauto. apply (Int64.signed_range (Int64.repr 0)).
                tauto.
            }
            tauto.
         -- exists i1.
            split.
            {
                exists i2, (Int64.repr 0).
                split. apply (IHe s (Pointer (Union name0)) i2). tauto.
                split. split. tauto. apply (Int64.signed_range (Int64.repr 0)).
                tauto.
            }
            tauto.
  + unfold ERefineRel in IHe. unfold ERefineRel.
    intros.
    split; simpl; try tauto.
    - intros.
      unfold member_sem_nrm,arith_compute1_nrm in H.
      unfold DntSem_WhileD_malloc.arith_sem1_nrm.
      unfold DntSem_WhileD_malloc.arith_compute1_nrm.
      destruct H as [t1 [i1 [to [? ?] ] ] ].
      destruct t1; simpl in H0;try tauto;
      destruct t1; simpl in H0; try tauto.
      unfold offset_p; simpl;
      simpl;try tauto.
      ++ apply (L sudef envt e s (Pointer (Struct name0)) i1) in H as ?.
         rewrite <- H1.
         unfold offset.
         destruct (SDef sudef name0);simpl.
         -- exists i1, (Int64.repr (calc_offset l mem0 (size sudef))).
            split. apply (IHe s (Pointer (Struct name0)) i1). tauto.
            split; tauto.
         -- tauto.
      ++ apply (L sudef envt e s (Pointer (Union name0)) i1) in H as ?. 
         rewrite <- H1.
         unfold offset.
         destruct (UDef sudef name0);simpl.
         -- exists i1, (Int64.repr 0).
            split. apply (IHe s (Pointer (Union name0)) i1). tauto.
            split. split. tauto. apply (Int64.signed_range (Int64.repr 0)).
            tauto.
         -- tauto.
    - intros.
      unfold member_sem_nrm,arith_compute1_nrm,deref_sem_nrm in H.
      unfold DntSem_WhileD_malloc.arith_sem1_nrm.
      unfold DntSem_WhileD_malloc.arith_compute1_nrm.
      unfold DntSem_WhileD_malloc.deref_sem_nrm.
      destruct H as [t1 [i1 [ [t2 [i2 [to [? ?] ] ] ] [_ ?] ] ] ];
      destruct t2; simpl in H0; try tauto;
      destruct t2; simpl in H0; try tauto;
      unfold offset_p; simpl;
      simpl;try tauto.
      ++ apply (L sudef envt e s (Pointer (Struct name0)) i2) in H as ?.
         rewrite <- H2.
         unfold offset.
         destruct (SDef sudef name0);simpl.
         -- exists i1.
            split. 
            {
                exists i2,(Int64.repr (calc_offset l mem0 (size sudef))).
                split. apply (IHe s(Pointer (Struct name0)) i2). tauto.
                tauto.
            }
            tauto.
         -- exists i1.
            split.
            {
                exists i2, (Int64.repr 0).
                split. apply (IHe s (Pointer (Union name0)) i2). tauto.
                split. split. tauto. apply (Int64.signed_range (Int64.repr 0)).
                tauto.
            }
            tauto.
      ++ apply (L sudef envt e s (Pointer (Union name0)) i2) in H as ?.
         rewrite <- H2.
         unfold offset.
         destruct (UDef sudef name0);simpl.
         -- exists i1.
            split. 
            {
                exists i2, (Int64.repr 0).
                split. apply (IHe s (Pointer (Union name0)) i2). tauto.
                split. split. tauto. apply (Int64.signed_range (Int64.repr 0)).
                tauto.
            }
            tauto.
         -- exists i1.
            split.
            {
                exists i2, (Int64.repr 0).
                split. apply (IHe s (Pointer (Union name0)) i2). tauto.
                split. split. tauto. apply (Int64.signed_range (Int64.repr 0)).
                tauto.
            }
            tauto.
Qed.

Notation "x '.(cnrm)'" := (DntSem_WhileD_malloc.CDenoteDmalloc.nrm x)
  (at level 1, only printing).
Notation "x '.(cinf)'" := (DntSem_WhileD_malloc.CDenoteDmalloc.inf x)
  (at level 1, only printing).

Ltac any_cnrm x := exact (DntSem_WhileD_malloc.CDenoteDmalloc.nrm x).
Ltac any_cinf x := exact (DntSem_WhileD_malloc.CDenoteDmalloc.inf x).
Notation "x '.(cnrm)'" := (ltac:(any_cnrm x))
  (at level 1, only parsing).
Notation "x '.(cinf)'" := (ltac:(any_cinf x))
  (at level 1, only parsing).

(**程序语句的精化关系，要求前者的 nrm 和 inf 分别是后者的子集**)
Definition CRefineRel (sudef: SUDef) (envt: var_name -> Types) (c1: Lang_WhileDU1.com) (c2: Lang_WhileD_malloc.com): Prop :=
  (forall s t,
    (DntSem_WhileDU1.eval_com sudef envt c1).(nrm) s t ->
    (DntSem_WhileD_malloc.eval_com c2).(cnrm) s t) /\
  (forall s,
    (DntSem_WhileDU1.eval_com sudef envt c1).(inf) s ->
    (DntSem_WhileD_malloc.eval_com c2).(cinf) s).

(**简化证明用**)
Lemma ERefineRel_l:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e1: expr) (e2: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e1 e2 ->
  forall s t i,
    (eval_l sudef envt e1).(nrm) s t i ->
    (DntSem_WhileD_malloc.eval_l e2).(mnrm) s i.
Proof. unfold ERefineRel. intros. pose proof H s t i as H. tauto. Qed.

Lemma ERefineRel_r:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e1: expr) (e2: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e1 e2 ->
  forall s t i,
    (eval_r sudef envt e1).(nrm) s t i ->
    (DntSem_WhileD_malloc.eval_r e2).(mnrm) s i.
Proof. unfold ERefineRel. intros. pose proof H s t i as H. tauto. Qed.

Lemma ERefineRel_tt:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e1: expr) (e2: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e1 e2 ->
  forall s t,
    test_true (eval_r sudef envt e1) s t ->
    DntSem_WhileD_malloc.test_true (DntSem_WhileD_malloc.eval_r e2) s t.
Proof. 
unfold ERefineRel. intros. 
unfold test_true in H0. simpl in H0.
unfold DntSem_WhileD_malloc.test_true. simpl.
destruct H0 as [ [T [i ?] ] ?].
specialize (H s T i).
split. exists i. tauto.
tauto.
Qed.

Lemma ERefineRel_tf:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e1: expr) (e2: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e1 e2 ->
  forall s t,
    test_false (eval_r sudef envt e1) s t ->
    DntSem_WhileD_malloc.test_false (DntSem_WhileD_malloc.eval_r e2) s t.
Proof. 
unfold ERefineRel. intros. 
unfold test_false in H0. simpl in H0.
unfold DntSem_WhileD_malloc.test_false. simpl.
destruct H0 as [ [T ? ] ?].
specialize (H s T (Int64.repr 0)).
split. tauto.
tauto.
Qed.

Lemma CRefineRel_nrm:
forall (sudef: SUDef) (envt: var_name -> Types)
  (c1: com) (c2: Lang_WhileD_malloc.com),
  CRefineRel sudef envt c1 c2 ->
  forall s t : state,
 (eval_com sudef envt c1).(nrm) s t ->
 (DntSem_WhileD_malloc.eval_com c2).(cnrm) s t.
Proof. unfold CRefineRel. intros. destruct H as [H _]. pose proof H s t. tauto. Qed.

Lemma CRefineRel_inf:
forall (sudef: SUDef) (envt: var_name -> Types)
  (c1: com) (c2: Lang_WhileD_malloc.com),
  CRefineRel sudef envt c1 c2 ->
  forall s: state,
 (eval_com sudef envt c1).(inf) s ->
 (DntSem_WhileD_malloc.eval_com c2).(cinf) s.
Proof. unfold CRefineRel. intros. destruct H as [_ H]. pose proof H s. tauto. Qed.

Lemma RefineRel_boundedLB:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e1: expr) (e2: Lang_WhileD_malloc.expr)
  (c1: com) (c2: Lang_WhileD_malloc.com),
  ERefineRel sudef envt e1 e2 -> 
  CRefineRel sudef envt c1 c2 ->
  forall i s t,
  boundedLB_nrm (eval_r sudef envt e1) (eval_com sudef envt c1) i s t ->
  DntSem_WhileD_malloc.boundedLB_nrm (DntSem_WhileD_malloc.eval_r e2) (DntSem_WhileD_malloc.eval_com c2) i s t.
Proof.
intros sudef envt e1 e2 c1 c2 ? ?.
induction i.
+ tauto.
+ intros.
unfold boundedLB_nrm in H1. Sets_unfold in H1. simpl in H1.
unfold DntSem_WhileD_malloc.boundedLB_nrm. Sets_unfold. simpl.
pose proof ERefineRel_tt _ _ _ _ H as Ht.
pose proof ERefineRel_tf _ _ _ _ H as Hf.
pose proof CRefineRel_nrm _ _ _ _ H0 as Hn.
destruct H1 as [ [i0 [? [i1 ?] ] ]| ?].
  - left.
    exists i0.
    split. apply (Ht s i0). tauto.
    exists i1.
    specialize (Hn i0 i1).
    specialize (IHi i1 t).
    tauto.
  - right. 
    apply (Hf s t). tauto.
Qed.

(**证明程序语句中对应的结构保持精化关系**)

Lemma CSkip_RR:
forall (sudef: SUDef) (envt: var_name -> Types),
  CRefineRel sudef envt (CSkip) (Lang_WhileD_malloc.CSkip).
Proof.
intros.
unfold CRefineRel. tauto.
Qed.

Lemma CAsgnDeref_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e11 e12: expr) (e21 e22: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e11 e21 ->
  ERefineRel sudef envt e12 e22 ->
  CRefineRel sudef envt (CAsgnDeref e11 e12) (Lang_WhileD_malloc.CAsgnDeref e21 e22).
Proof.
intros.
pose proof ERefineRel_r _ _ _ _ H. clear H.
pose proof ERefineRel_r _ _ _ _ H0. clear H0.
unfold CRefineRel.
split.
+ intros.
  simpl in H0. unfold asgn_deref_sem_nrm in H0.
  unfold DntSem_WhileD_malloc.eval_com. simpl.
  unfold DntSem_WhileD_malloc.asgn_deref_sem_nrm.
  destruct H0 as [t1 [i1 [t2 [i2 ?] ] ] ].
  exists i1,i2.
  specialize (H1 s t1 i1).
  specialize (H s t2 i2).
  tauto.
+ tauto.
Qed.

Lemma CAsgnVar_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types)
  (X: var_name) (e1: expr) (e2: Lang_WhileD_malloc.expr),
  ERefineRel sudef envt e1 e2 ->
  CRefineRel sudef envt (CAsgnVar X e1) (Lang_WhileD_malloc.CAsgnVar X e2).
Proof.
intros.
pose proof ERefineRel_r _ _ _ _ H. clear H.
unfold CRefineRel.
split.
+ intros.
  simpl in H. unfold asgn_deref_sem_nrm in H.
  simpl. unfold DntSem_WhileD_malloc.asgn_deref_sem_nrm.
  destruct H as [t1 [i1 [t2 [i2 ?] ] ] ].
  exists i1,i2.
  specialize (H0 s t2 i2).
  tauto.
+ tauto.
Qed. 

Lemma CSeq_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types)
  (c11 c12: com) (c21 c22: Lang_WhileD_malloc.com),
  CRefineRel sudef envt c11 c21 ->
  CRefineRel sudef envt c12 c22 ->
  CRefineRel sudef envt (CSeq c11 c12) (Lang_WhileD_malloc.CSeq c21 c22).
Proof.
intros.
pose proof CRefineRel_nrm _ _ _ _ H as Hn1.
pose proof CRefineRel_inf _ _ _ _ H as Hi1.
pose proof CRefineRel_nrm _ _ _ _ H0 as Hn2.
pose proof CRefineRel_inf _ _ _ _ H0 as Hi2.
unfold CRefineRel.
split; intros; 
simpl in H1; Sets_unfold in H1;
simpl; Sets_unfold.
+ destruct H1.
  exists x.
  specialize (Hn1 s x).
  specialize (Hn2 x t).
  tauto.
+ destruct H1 as [? | [b ?] ].
  - left. apply (Hi1 s). tauto.
  - right. 
    specialize (Hn1 s b).
    specialize (Hi2 b).
    exists b.
    tauto.
Qed.

Lemma CIf_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e1: expr) (c11 c12: com)
  (e2: Lang_WhileD_malloc.expr) (c21 c22: Lang_WhileD_malloc.com),
  ERefineRel sudef envt e1 e2 ->
  CRefineRel sudef envt c11 c21 ->
  CRefineRel sudef envt c12 c22 ->
  CRefineRel sudef envt (CIf e1 c11 c12) (Lang_WhileD_malloc.CIf e2 c21 c22).
Proof.
intros.
pose proof ERefineRel_tt _ _ _ _ H as Ht.
pose proof ERefineRel_tf _ _ _ _ H as Hf.
pose proof CRefineRel_nrm _ _ _ _ H0 as Hn1.
pose proof CRefineRel_inf _ _ _ _ H0 as Hi1.
pose proof CRefineRel_nrm _ _ _ _ H1 as Hn2.
pose proof CRefineRel_inf _ _ _ _ H1 as Hi2.
unfold CRefineRel.
split; intros;
simpl in H2; Sets_unfold in H2;
simpl; Sets_unfold.
+ destruct H2 as [ [i1 [? ?] ]|[i2 [? ?] ] ].
  - left. exists i1.
    specialize (Ht s i1).
    specialize (Hn1 i1 t).
    tauto.
  - right. exists i2.
    specialize (Hf s i2).
    specialize (Hn2 i2 t).
    tauto.
+ destruct H2 as [ [i1 [? ?] ]|[i2 [? ?] ] ].
  - left. exists i1.
    specialize (Ht s i1).
    specialize (Hi1 i1).
    tauto.
  - right. exists i2.
    specialize (Hf s i2).
    specialize (Hi2 i2).
    tauto.
Qed.

Lemma CWhile_persistRR:
forall (sudef: SUDef) (envt: var_name -> Types)
  (e1: expr) (c1: com)
  (e2: Lang_WhileD_malloc.expr) (c2: Lang_WhileD_malloc.com),
  ERefineRel sudef envt e1 e2 ->
  CRefineRel sudef envt c1 c2 ->
  CRefineRel sudef envt (CWhile e1 c1) (Lang_WhileD_malloc.CWhile e2 c2).
Proof.
intros.
pose proof ERefineRel_tt _ _ _ _ H as Ht.
pose proof ERefineRel_tf _ _ _ _ H as Hf.
pose proof CRefineRel_nrm _ _ _ _ H0 as Hn.
pose proof CRefineRel_inf _ _ _ _ H0 as Hi.
unfold CRefineRel.
split; intros;
simpl in H1; Sets_unfold in H1;
simpl; Sets_unfold.
+ destruct H1 as [i ?].
  exists i.
  apply (RefineRel_boundedLB _ _ _ _ _ _ H H0 i s t).
  tauto.
+ destruct H1 as [X ?].
  exists X.
  unfold is_inf in H1. Sets_unfold in H1. simpl in H1.
  unfold DntSem_WhileD_malloc.is_inf. Sets_unfold. simpl.
  split.
  {
    intros.
    destruct H1.
    specialize (H1 a).
    apply H1 in H2. clear H1.
    destruct H2 as [b [? [? | ? ] ] ];
    exists b; 
    specialize (Ht a b);
    split; try tauto.
    - destruct H2 as [b0 ?].
      specialize (Hn b b0).
      left. exists b0. tauto.
    - specialize (Hi b).
      right. tauto.
  }
  tauto.
Qed.

(**定义程序语句的变换**)
(**Print com.
Print Lang_WhileD_malloc.com.**)
(**WhileDU1 中的结构体变量变为分配内存长度为 sizeof Type 的局部变量，其地址为首地址**)
Fixpoint CTransform
  (sudef: SUDef) (envt: var_name -> Types)
  (c: com): Lang_WhileD_malloc.com:=
  match c with
  | CSkip => Lang_WhileD_malloc.CSkip
  | CAsgnVar x e =>
      Lang_WhileD_malloc.CAsgnVar x (ETransform sudef envt e)
  | CAsgnDeref e1 e2 =>
      Lang_WhileD_malloc.CAsgnDeref (ETransform sudef envt e1)(ETransform sudef envt e2)
  | CSeq c1 c2 =>
      Lang_WhileD_malloc.CSeq (CTransform sudef envt c1) (CTransform sudef envt c2)
  | CIf e c1 c2 =>
      Lang_WhileD_malloc.CIf (ETransform sudef envt e)
        (CTransform sudef envt c1) (CTransform sudef envt c2)
  | CWhile e c =>
      Lang_WhileD_malloc.CWhile (ETransform sudef envt e) (CTransform sudef envt c)
  | CLocalVar t x c =>
      Lang_WhileD_malloc.CLocalVarMalloc x 
        (Lang_WhileD_malloc.EConst (sizeof t sudef))
        (CTransform sudef (new_local envt x t) c)
  | CAsgnMember e1 e2 =>
      match (ETransform sudef envt e1) with
      | Lang_WhileD_malloc.EDeref e =>
          Lang_WhileD_malloc.CAsgnDeref e (ETransform sudef envt e2)
      | _ => Lang_WhileD_malloc.CSkip
      end
  end.

(**证明程序语句的变换服从精化关系**)
Theorem CTransform_RefineRel:
forall (c: com),
  forall (sudef: SUDef) (envt: var_name -> Types),
    CRefineRel sudef envt c (CTransform sudef envt c).
Proof.
induction c.
+ simpl. apply CSkip_RR.
+ simpl in *.
  unfold CRefineRel in *.
  intros. split.
  - intros.
    simpl in H. unfold local_sem_nrm in H.
    simpl. unfold DntSem_WhileD_malloc.local_sem_nrm.
    exists (Int64.repr (sizeof t sudef)).
    destruct H as [? [? ?] ].
    exists x0.
    split.
    * split; [reflexivity | apply H].
    * sets_unfold. sets_unfold in H0.
      destruct H0 as [i [? [i0 [? ?] ] ] ].
      exists i.
      split; [apply H0 | ].
      exists i0.
      split; [| apply H2].
      pose proof IHc sudef (new_local envt x t) as IH. destruct IH as [IH _]. clear IHc.
      pose proof IH i i0 as IH.
      apply IH. apply H1.
  - intros.
    simpl in H. unfold local_sem_inf in H.
    simpl. unfold DntSem_WhileD_malloc.local_sem_inf.
    sets_unfold. sets_unfold in H.
    destruct H as [? [i2 [b [? ?] ] ] ].
    exists (Int64.repr (sizeof t sudef)).
    split; try tauto.
    exists i2. exists b.
    split; [apply H0|].
    pose proof IHc sudef (new_local envt x t) as IH. destruct IH as [_ IH]. clear IHc.
    pose proof IH b as IH.
    apply IH. apply H1.
+ simpl. intros.
  apply CAsgnVar_persistRR.
  apply ETransform_RefineRel.
+ simpl. intros.
  unfold CRefineRel.
  destruct e1; simpl; Sets_unfold ; try tauto;
  split; try tauto; intros.
  - unfold asgn_deref_sem_nrm in H. simpl in H.
    unfold DntSem_WhileD_malloc.asgn_deref_sem_nrm. simpl.
    destruct H as [t1 [i1 [t2 [i2 ?] ] ] ].
    exists i1, i2.
    split.
    * destruct H as [? _]. 
      unfold member_sem_nrm in H.
      unfold arith_compute1_nrm in H.
      simpl in H.
      unfold DntSem_WhileD_malloc.arith_sem1_nrm. 
      unfold DntSem_WhileD_malloc.arith_compute1_nrm.
      simpl.
      destruct H as [t3 [i3 [to ?] ] ].
      exists i3.
      destruct H as [? ?].
      destruct t3; try tauto.
      destruct t3; try tauto.
      ++ pose proof ETransform_RefineRel sudef envt e1 s (Pointer (Struct name0)) i3.
         unfold offset_p. unfold offset. simpl.
         pose proof WhileDU1_DntSemnrm_TypeEq sudef envt e1 s (Pointer (Struct name0)) i3.
         apply H2 in H as ?. rewrite <- H3. simpl.
         simpl in H0.
         destruct (SDef sudef name0); try tauto.
         exists (Int64.repr (calc_offset l mem0 (size sudef))).
         tauto.
      ++ pose proof ETransform_RefineRel sudef envt e1 s (Pointer (Union name0)) i3.
         unfold offset_p. unfold offset. simpl.
         pose proof WhileDU1_DntSemnrm_TypeEq sudef envt e1 s (Pointer (Union name0)) i3.
         apply H2 in H as ?. rewrite <- H3. simpl.
         simpl in H0.
         destruct (UDef sudef name0); try tauto.
         exists (Int64.repr (0)).
         pose proof Int64.signed_range (Int64.repr (0)).
         tauto.
    * pose proof ETransform_RefineRel sudef envt e2 s t2 i2.
      tauto.
  - unfold asgn_deref_sem_nrm in H. simpl in H.
    unfold DntSem_WhileD_malloc.asgn_deref_sem_nrm. simpl.
    destruct H as [t1 [i1 [t2 [i2 ?] ] ] ].
    exists i1, i2.
    split.
    * destruct H as [? _]. 
      unfold member_sem_nrm in H.
      unfold arith_compute1_nrm in H.
      simpl in H.
      unfold DntSem_WhileD_malloc.arith_sem1_nrm. 
      unfold DntSem_WhileD_malloc.arith_compute1_nrm.
      simpl.
      destruct H as [t3 [i3 [to ?] ] ].
      exists i3.
      destruct H as [? ?].
      destruct t3; try tauto.
      destruct t3; try tauto.
      ++ pose proof ETransform_RefineRel sudef envt e1 s (Pointer (Struct name0)) i3.
         unfold offset_p. unfold offset. simpl.
         pose proof WhileDU1_DntSemnrm_TypeEq sudef envt e1 s (Pointer (Struct name0)) i3.
         apply H2 in H as ?. rewrite <- H3. simpl.
         simpl in H0.
         destruct (SDef sudef name0); try tauto.
         exists (Int64.repr (calc_offset l mem0 (size sudef))).
         tauto.
      ++ pose proof ETransform_RefineRel sudef envt e1 s (Pointer (Union name0)) i3.
         unfold offset_p. unfold offset. simpl.
         pose proof WhileDU1_DntSemnrm_TypeEq sudef envt e1 s (Pointer (Union name0)) i3.
         apply H2 in H as ?. rewrite <- H3. simpl.
         simpl in H0.
         destruct (UDef sudef name0); try tauto.
         exists (Int64.repr (0)).
         pose proof Int64.signed_range (Int64.repr (0)).
         tauto.
    * pose proof ETransform_RefineRel sudef envt e2 s t2 i2.
      tauto.
+ simpl. intros.
  apply CAsgnDeref_persistRR;
  apply ETransform_RefineRel.
+ simpl. intros.
  apply CSeq_persistRR;
  [apply IHc1|apply IHc2].
+ simpl. intros.
  apply CIf_persistRR.
  - apply ETransform_RefineRel.
  - apply IHc1. - apply IHc2.
+ simpl. intros.
  apply CWhile_persistRR.
  - apply ETransform_RefineRel.
  - apply IHc.
Qed.

End RefineRel.