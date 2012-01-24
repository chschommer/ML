(*Mein ML*)

(*Implemtiert ist: logisches AND, OR, NOT, autom. TypCasting (real nach Int), Tupel, div, mod, Gleitkomma-Divion*)


(*Hilfsprozedur: *)
fun RealfromInt' (0, a , bool) = if bool then ~a else a
   |RealfromInt' (n, a , bool) = RealfromInt'(n-1, a+1.0, bool)

fun RealfromInt a = if a<0 then RealfromInt'(~a, 0.0, true) else RealfromInt'(a,0.0,false)


(*Hilfsprozedur/*)

datatype con = False | True | IC of int | RC of real
type id = string
datatype opr = Add | Sub | Mul | Leq | AND | OR | Div | Mod | GDiv 
datatype UnOp = NOT 

datatype ty = Bool | Int | Arrow of ty * ty | Real | TupelTyp of ty list

datatype exp = 
     Con of con
   | Id of id
   | UOp of UnOp * exp
   | Opr of opr * exp * exp
   | If of exp * exp * exp
   | Abs of id * ty * exp
   | App of exp * exp
   | Tupel of exp list



type 'a env = id -> 'a

exception Unbound of id
fun empty x = raise Unbound x

fun update env x a y = if y=x then a else env y

exception Error of string

(*elab*)

fun elabCon True   = Bool
   |elabCon False  = Bool
   |elabCon (IC _) = Int
   |elabCon (RC _) = Real

fun elabU NOT Bool = Bool
   |elabU _   _    = raise Error "T Unop"
   
fun elabOpr Add Int  Int   = Int
   |elabOpr Add Int  Real  = Real
   |elabOpr Add Real Int   = Real
   |elabOpr Add Real Real  = Real
   |elabOpr Sub Int  Int   = Int
   |elabOpr Sub Real Int   = Real
   |elabOpr Sub Int  Real  = Real
   |elabOpr Sub Real Real  = Real	
   |elabOpr Mul Int  Int   = Int
   |elabOpr Mul Real Int   = Real
   |elabOpr Mul Int  Real  = Real
   |elabOpr Mul Real Real  = Real
   |elabOpr Leq Int  Int   = Bool
   |elabOpr Leq Real Int   = Bool
   |elabOpr Leq Int  Real  = Bool
   |elabOpr Leq Real Real  = Bool
   |elabOpr AND Bool Bool  = Bool
   |elabOpr OR  Bool Bool  = Bool
   |elabOpr Div Int Int    = Int
   |elabOpr Mod Int Int    = Int
   |elabOpr GDiv Int Real  = Real
   |elabOpr GDiv Real Real = Real
   |elabOpr GDiv Real Int  = Real
   |elabOpr GDiv Int Int   = Real
   |elabOpr _    _   _     = raise Error "T Opr" 

fun elab f (Con c)          = elabCon c
   |elab f (Id x)           = f x
   |elab f (Tupel xs)       = TupelTyp (foldl (fn(m,s) => s@ [elab empty m] ) ( nil) xs )
   |elab f (Opr(opr, e1, e2)) = elabOpr opr (elab f e1) (elab f e2)
   |elab f (UOp(uno, e1))   = elabU uno (elab f e1)
   |elab f (If(e1,e2,e3))   = 
                     (case (elab f e1, elab f e2, elab f e3) of 
                           (Bool, t2, t3) => if t2=t3 then t2 else raise Error "T If1 Typ 2 != Typ 3"
                     | _ => raise Error "T If2 Sonst iwas falsch")
   |elab f (Abs(x,t,e))     = Arrow(t, elab (update f x t) e)
   |elab f (App(e1,e2))     = (case elab f e1 of 
                               Arrow(t,t') => if t = elab f e2 then t' 
                               else raise Error "T App1 Typen Stimmen nicht"
    			      | _ => raise Error "T App 2")                        



(*eval*)

datatype value = IV of int | RV of real |TV of value list
              | Proc of id * exp * value env

fun evalCon False  = IV 0
   |evalCon True   = IV 1
   |evalCon (IC x) = IV x
   |evalCon (RC x) = RV x

fun evalU NOT (IV x) = IV(if x=0 then 1 else 0)
   |evalU _       _  = raise Error "R UnOpr"

fun evalOpr Add (IV x) (IV y)  = IV(x+y)
   |evalOpr Add (RV x) (IV y)  = RV( x + (RealfromInt y))
   |evalOpr Add (IV x) (RV y)  = RV((RealfromInt x) + y)
   |evalOpr Add (RV x) (RV y)  = RV(x+y)
   |evalOpr Sub (IV x) (IV y)  = IV(x-y)
   |evalOpr Sub (RV x) (IV y)  = RV(x - (RealfromInt y))
   |evalOpr Sub (IV x) (RV y)  = RV((RealfromInt x) - y)
   |evalOpr Sub (RV x) (RV y)  = RV(x-y)
   |evalOpr Mul (IV x) (IV y)  = IV(x*y)
   |evalOpr Mul (RV x) (IV y)  = RV( x *  (RealfromInt y))
   |evalOpr Mul (IV x) (RV y)  = RV((RealfromInt x) * y)
   |evalOpr Mul (RV x) (RV y)  = RV(x*y)
   |evalOpr Leq (IV x) (IV y)  = IV(if x<=y then 1 else 0)
   |evalOpr Leq (RV x) (IV y)  = IV(if x<= (RealfromInt y) then 1 else 0)
   |evalOpr Leq (IV x) (RV y)  = IV(if (RealfromInt x) <= y then 1 else 0)
   |evalOpr Leq (RV x) (RV y)  = IV(if x<=y then 1 else 0)
   |evalOpr AND (IV x) (IV y)  = IV(case (x,y) of (1,1) => 1 | _ => 0)
   |evalOpr OR  (IV x) (IV y)  = IV(case (x,y) of (0,0) => 0 | _ => 1)
   |evalOpr Div (IV x) (IV y)  = if y=0 then raise Error "R Opr div durch 0" else IV(x div y)
   |evalOpr Mod (IV x) (IV y)  = if y=0 then raise Error "R Opr mod durch 0" else IV(x mod y) 
   |evalOpr GDiv (IV x) (IV y) = if y=0 then raise Error "R Opr GDiv durch 0" else RV((RealfromInt x) / (RealfromInt y))
   |evalOpr GDiv (RV x) (IV y) = if y=0 then raise Error "R Opr GDiv durch 0" else RV(x / (RealfromInt y))
   |evalOpr GDiv (IV x) (RV y) = if y=0.0 then raise Error "R Opr GDiv durch 0" else RV((RealfromInt x) / y)
   |evalOpr GDiv (RV x) (RV y) = if y=0.0 then raise Error "R Opr GDiv durch 0" else RV(x/y)
   |evalOpr _     _       _    = raise Error "R Opr"

fun eval f (Con c) = evalCon c
   |eval f (Id x)  = f x
   |eval f (Tupel xs) = TV(foldl (fn(m,s) => s @ [eval empty m]) nil xs)
   |eval f (UOp(uno, e1))   = evalU uno (eval f e1)
   |eval f (Opr(opr,x,y)) = evalOpr opr (eval f x) (eval f y)
   |eval f (If(b,x,y))   = (case eval f b of
                              IV 1 => eval f x
                             |IV 0 => eval f y
                             | _   => raise Error "R If Kein Bool an Pos 1")
   |eval f (Abs(x,t,e))  = Proc(x,e,f)
   |eval f (App(e1,e2))  = (case (eval f e1, eval f e2) of 
                                              (Proc(x,e,f'), v) => eval (update f' x v) e
                                            | _ => raise Error "R App")


(*Testsuite*)

datatype Test = Bestanden | Durchgefallen

fun V2Int (IV x) = x
fun V2Real (RV x) = x

fun check xs = if (foldl (fn(m,s) => if m=s then true else false) true xs) then Bestanden else Durchgefallen

val Arith = [V2Real(eval empty (Opr(Add,Con (RC 6.648700471127845),Con (RC 8.959234998406282)))) = 6.648700471127845 + 8.959234998406282,
V2Real(eval empty (Opr(Sub,Con (RC 5.002604629400707),Con (RC 7.94417247348976)))) = 5.002604629400707 - 7.94417247348976,
V2Real(eval empty (Opr(Mul,Con (RC 6.121988566364697),Con (RC 9.532579459619745)))) = 6.121988566364697 * 9.532579459619745,
V2Real(eval empty (Opr(GDiv,Con (RC 4.328138364910766),Con (RC 8.34908662220213)))) = 4.328138364910766 / 8.34908662220213,
V2Real(eval empty (Opr(Add,Con (RC 2.6418304466952334),Con (RC 5.971974752269481)))) = 2.6418304466952334 + 5.971974752269481,
V2Real(eval empty (Opr(Sub,Con (RC 7.620129444920983),Con (RC 6.289793266693588)))) = 7.620129444920983 - 6.289793266693588,
V2Real(eval empty (Opr(Mul,Con (RC 0.5066347008993088),Con (RC 5.892610828782186)))) = 0.5066347008993088 * 5.892610828782186,
V2Real(eval empty (Opr(GDiv,Con (RC 2.8641371327725684),Con (RC 4.768924909083595)))) = 2.8641371327725684 / 4.768924909083595,
V2Real(eval empty (Opr(Add,Con (RC 8.976874103706862),Con (RC 7.6694776297806015)))) = 8.976874103706862 + 7.6694776297806015,
V2Real(eval empty (Opr(Sub,Con (RC 2.739450432904257),Con (RC 7.124712911994047)))) = 2.739450432904257 - 7.124712911994047,
V2Real(eval empty (Opr(Mul,Con (RC 3.6960953085940584),Con (RC 1.796597956054603)))) = 3.6960953085940584 * 1.796597956054603,
V2Real(eval empty (Opr(GDiv,Con (RC 6.343580210489089),Con (RC 7.1724376215663765)))) = 6.343580210489089 / 7.1724376215663765,
V2Real(eval empty (Opr(Add,Con (RC 3.031405091114939),Con (RC 2.6638598929355304)))) = 3.031405091114939 + 2.6638598929355304,
V2Real(eval empty (Opr(Sub,Con (RC 3.8325983228326654),Con (RC 0.08529250727116966)))) = 3.8325983228326654 - 0.08529250727116966,
V2Real(eval empty (Opr(Mul,Con (RC 4.947760827625598),Con (RC 2.911187331511197)))) = 4.947760827625598 * 2.911187331511197,
V2Real(eval empty (Opr(GDiv,Con (RC 9.655121519226412),Con (RC 5.339425568018843)))) = 9.655121519226412 / 5.339425568018843,
V2Real(eval empty (Opr(Add,Con (RC 4.9229544535031176),Con (RC 1.240472904560861)))) = 4.9229544535031176 + 1.240472904560861,
V2Real(eval empty (Opr(Sub,Con (RC 0.7315673089162855),Con (RC 8.799885584200217)))) = 0.7315673089162855 - 8.799885584200217,
V2Real(eval empty (Opr(Mul,Con (RC 4.365272187566368),Con (RC 9.848913310016009)))) = 4.365272187566368 * 9.848913310016009,
V2Real(eval empty (Opr(GDiv,Con (RC 5.666626635300766),Con (RC 8.338641586227983)))) = 5.666626635300766 / 8.338641586227983]

val castTest = 
[V2Real(eval empty (Opr(Add,Con (RC 7.194687636777993),Con (IC 2)))) = 7.194687636777993 + RealfromInt 2,
V2Real(eval empty (Opr(Sub,Con (RC 3.193768984182489),Con (IC 7)))) = 3.193768984182489 - RealfromInt 7,
V2Real(eval empty (Opr(Mul,Con (RC 0.9153632754853458),Con (IC 5)))) = 0.9153632754853458 * RealfromInt 5,
V2Real(eval empty (Opr(GDiv,Con (RC 8.532297203530153),Con (IC 7)))) = 8.532297203530153 / RealfromInt 7,
V2Real(eval empty (Opr(Add,Con (IC 5),Con (RC 1.82688258821593)))) = RealfromInt 5 + 1.82688258821593,
V2Real(eval empty (Opr(Sub,Con (IC 8),Con (RC 9.420227886883177)))) = RealfromInt 8 - 9.420227886883177,
V2Real(eval empty (Opr(Mul,Con (IC 5),Con (RC 3.531406748570387)))) = RealfromInt 5 * 3.531406748570387,
V2Real(eval empty (Opr(GDiv,Con (IC 3),Con (RC 3.9441315070073135)))) = RealfromInt 3 / 3.9441315070073135]



fun artTest () = check Arith            (*Test für arith. Ausdrücke*)
fun CastingTest() = check castTest      (*Test für das aut. Typ casten*)

