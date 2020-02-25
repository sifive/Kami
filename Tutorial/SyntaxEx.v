Require Import Kami.AllNotations.

(* In order to write a Kami module, one first opens a section using the same name as the module,
  and writes the following five lines of boiler plate code. *)
(* Notation "'IfE' cexpr 'then' tact 'else' fact 'as' name ; cont " := *)
(*   (IfElseE cexpr%kami_expr tact fact (fun name => cont)) *)
(*     (at level 14, right associativity) : kami_expr_scope. *)
(* Notation "'IfE' cexpr 'then' tact 'else' fact ; cont " := *)
(*   (IfElse cexpr%kami_expr tact fact (fun _ => cont)) *)
(*     (at level 14, right associativity) : kami_expr_scope. *)
(* Notation "'IfE' cexpr 'then' tact ; cont" := *)
(*   (IfElse cexpr%kami_expr tact (RetE (Const _ Default))%kami_expr (fun _ => cont)) *)
(*     (at level 14, right associativity) : kami_expr_scope. *)


Section exampleModule.
  Variable name : string.
  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  (* All names in this module will be prepended by a unique name to avoid duplication of names.
    In Kami, all names should be globally unique, and therefore requires this to be done explicitly.
    Inside a module, any @^"newName" will be automatically converted into name ++ "_" ++ "newName".
    The next two lines are added because the Notations in Coq are broken. *)

  Definition exampleModule :=
    MODULE {
      Register @^"reg1": Bool <- false
      (* register named reg1 of type Bool, initialized to false *)
      
      with Register @^"reg2": Bit 20 <- (20'h"7abcd")
      (* 20'h"7abcd" initializes reg2 to 20 bits represented by the hex 0x7abcd *)
      
      with Register @^"reg3": Array 5 (Bit 8) <-
      (ARRAY_CONST { 8'h"a4"; 8'h"b3"; 8'h"5e"; 8'h"34"; 8'h"45" })
      (* reg3 is initialized to an array containing 5 (Bit 8) elements *)
      
      with Register @^"reg4": STRUCT_TYPE {
        "field1" :: Bit 4 ;
        "someOtherField" :: Bool } <-
      STRUCT_CONST {
        "field1" ::= natToWord _ 13 ;
        "someOtherField" ::= true }
      (* reg4 is initialized to a "structure" containing fields "field1" and "someOtherField".
        "field1" is initialized to (natToWord _ 13), which is converting a nat 13 into a bit-vector (i.e. [word]) of length 4
        (the number of bits is automatically inferred by Coq's type checker based on the type of "field1" being Bit 4),
         and "someOtherField" to true *)
      
      with RegisterU @^"reg5" : Bool
      (* Uninitialized register reg5 *)
      
      with RegisterU @^"reg6" : Bool
      (* Uninitialized register reg6, for use later *)
      
      with Rule @^"rule1" := (
                                
        LET x1 : Bit 20 <- $3 + $4;
        (* Define a new temporary variable x1 of type Bit 10, whose value is computed by adding 3 with 4
          Note that 3 and 4 are converted into bit-vectors of width 10 using the "$" operator.
          The bit-width of 20 is automatically computed for the $ operator using the type information for x1.
          It is an error to add differently sized bit vectors
          *)
        
        LET x2 : Bool <- $$ false ;
        (* Another temporary variable x2, which is set to false. Notice the two $$ in case of creating a non-nat
          constant *)
        
        LET x3 : Array 2 Bool <- $$ ARRAY_CONST {false ; true} ;
        (* x3 is set to a 2-element array with boolean values. Notice
          agian that we use $$ for creating a non-not constant *)
        
        LET x4 : Array 2 (Bit 4) <- $$ ARRAY_CONST { $5 ; (natToWord 4 12)} ;
        (* yet another example of a constant array built using bit-vectors.
          The Coq's type checker fails to infer the width of the bit-vector this time, forcing us
          to specify the size as 4 *)
        
        LET x5 : STRUCT_TYPE {
          "sth1" :: Bool ;
          "sth2" :: Bit 20 } <-
        $$ STRUCT_CONST {
          "sth1" ::= false ;
          "sth2" ::= natToWord 20 4 };
        (* One can also have constant structures assigned to a local variable *)
        
        LET x6 <- 
        $$ STRUCT_CONST {
          "sth1" ::= false ;
          "sth2" ::= natToWord 20 4
          };
        (* One can omit the type of the expression if it is easy for Coq to infer it *)
        
        LET x7 <- #x1 + #x6@%"sth2";
        (* This construct covers several syntactic concepts explained as follows:
          1. Locally bound variables can be used in constructing expressions
          (which can, for instance, be assigned to other variables)
          2. To use a variable bound earlier, we use #variable-name, as in, #x1 and #x6
          3. We can get a field of a struct using @% notation, as in, (#x6)@%"sth2".
          The parenthesis around #x6 can be omitted because # binds more tightly than @% *)

        Read x8: Bool <- @^"reg1";
        (* Reading reg1 and binding it to variable x8.
          The type is not mandatory but cannot be inferred by Coq unless there is a use of x8 that determines the type of x8.
          In particular, even though reg1 is declared to be a Bool, Coq cannot infer it when it is read (or written) in an action.
          It's a good idea to always specify the type for register reads (and writes) *)
        
        Write @^"reg1" : Bool <- !(#x8);
        (* Writing back the negation of x8 (which contained the value read from register reg1) into reg1.
          Note that !e gives the negation of boolean expression e *)

        (* Now, we will look at a LETA block below. It is different from the LET block -- one can perform various actions
          like reading an writing registers, etc, whereas a LET is simply binding an expression to a name *)
        LETA x9: Bool <- (
          Read x10 <- @^"reg2";
          LET pred : Bit 20 <- #x10 - #x1;                
          Write @^"reg2" <- #x10 - #x1;
          (* This performs 2s complement subtraction and sets the value to reg2 *)
          
          Ret (#pred == $2)
          (* This returns a value evaluated from the LETA block.
             All actions must end with a return statement.
            The == is an operation of expressions that checks if the two sides of the == are equal *)
          );
        
        LET x10 <- !(#x9);
        (* The bound variable x9 can be used just like any other LET-bounded or Register Read variable *)

        (* Next, we will look at if-then-else actions. The following code either writes true to reg5 or to reg6 depending on x10 *)
        If (#x10)
        then (
          Write @^"reg5" <- $$ true;
          (* if and else part of the if-then-else statement should also end with a return statement *)
          (* Retv is a syntactic sugar for returning a value of type Bit 0, which contains no information *)    
          Retv )
        else (
          Write @^"reg6" <- $$ true;
          Retv);
        
        (* Unlike conventional if-then-else, in Kami, they can also return a value which can be bound to a variable to be used later *)
        If (!#x10)
        then (
          Write @^"reg5" <- $$ false;
          LET x: Bit 5 <- $3;  
          Ret #x )
        else (
          Write @^"reg6" <- $$ true;
          LET y: Bit 5 <- $8;  
          Ret #y)
        as z; (* We bind the return of if-then-else to z *)
        
        (* We use the return of if-then-else in the rest of the actions, i.e. we use z *)
        LET x11 <- #z;
        
        (* It is also legal to omit the else part. But then, the if part cannot return any value that can be bound *)
        If (!#x10)
        then (
          Read x1 : Bool <- @^"reg1";
          (* Note that you can rebind the names - the most recent binding is the one that will be used when the name is referred *)
            
          Retv );
        
        Call x12 : Bool <- "extMeth1"(#x7: Bit 20);
        (* This construct creates an external method call *)
        
        Call "extMeth2"(#x7: Bit 20);
        (* If the method returns a Bit 0, then the return can be omitted *)
        
        Call x13: Bit 4 <- "extMeth3"();
        (* Similarly, if the method's argument is a Bit 0, then the argument can be omitted *)
        
        Call "extMeth4"();
        (* If the return value and argument are both of type Bit 0, both of them can be omitted *)
        
        (* Methods cannot take multiple arguments. If multiple values have to be passed, create a struct and pass it *)
        
        (* The return values of the methods are bound to the names before <- as appropriate. For instance, we can refer to x12 and x13 *)
        
        LET x14 <- #x13;
        LET x15: Bool <- !#x12;
        
        (* We can write display statements in Kami, which gets printed whenever the rule is executed *)
        (* We supply a list of entities to be printed to the System command *)
        System (
          DispString _ "Hello World\n" ::
                       
          DispString _ "Val1 Hex: " ::
          (* To display a kami expression all in hex: *)           
          DispHex #x13 :: 
          
          DispString _ "Val1 Binary: " ::
          (* To display a kami expression all in binary *)           
          DispBinary #x13 :: 
        
          DispString _ "Val1 Decimal: " ::
          (* To display a kami expression all in decimal *)           
          DispDecimal #x13 ::
          
          (* We can also display structs and arrays in hex, binary or decimal *)
          DispHex #x6 ::
          (* Structs are displayed as { fieldName1: val1; fieldName2: val2; ... }, where the values are in binary, decimal or hex *)
          
          DispHex #x3 ::
          (* Arrays are displayed as { 0: val1; fieldName2: 1; ...; fieldNameNMinus1: valNMinus1 },
            where the values are in binary, decimal or hex *)

          (* One can also finish execution in a System statment *)
          Finish _ ::
          (* This is useful when the System action is sitting in an if-then-else predicate,
            to finish simulation when the predicate is true *)
          
          nil);
        
        LET x100: Void <- $$ (ZToWord 0 0);
        (* Void is literally Bit 0, and WO is the only way to create a value of type Bit 0 *)       
               
        (* Finally, we end any action by a return statement *)
        Retv
        )
      
      (* One can write multiple rules, which may update the same register, but must call different methods *)                       
      with Rule @^"rule2" := (
        Write @^"reg1" : Bool <- $$ true ;
        Read x : Bit 20 <- @^"reg2";
        Call "extMeth2_2"(#x: _);                
        Retv
        )
      
      (* This rule showcases all the expressions one can write in Kami, unlike rule1, which showcased all the actions *)
      with Rule @^"rule3" := (
        LET x1: Bool <- $$ true ;
        LET x2: Bool <- $$ false ;
        
        (* Boolean Not *)
        LET x3 <- !#x1;
        
        (* Boolean And *)
        LET x4 <- #x1 && #x2 ;
        
        (* Boolean Or *)
        LET x5 <- #x1 || #x2 ;
        
        (* Boolean Xor *)
        LET x6 <- #x1 ^^ #x2 ;
        
        LET x7: Bit 10 <- $3;
        LET x8: Bit 10 <- $4;
        LET x9: Bit 20 <- $5;
        
        (* Bitwise inversion *)
        LET x10 <- ~#x7;
        
        (* And reduction, that is And all the bits in the bit vector *)
        LET x100 <- UniBit (UAnd _) #x10;
        
        (* Or reduction, that is Or all the bits in the bit vector *)
        LET x101 <- UniBit (UOr _) #x10;
        
        (* Or reduction, that is XZor all the bits in the bit vector *)
        LET x102 <- UniBit (UXor _) #x10;
        
        (* Bitwise subtraction, unsigned 2's complement *)
        LET x14 <- #x7 - #x8;
        
        (* Shift left logical *)
        LET x15 <- #x9 << #x8;
        
        (* Shift right logical *)
        LET x16 <- #x9 >> #x8;
        
        (* Shift right arithmetic *)
        LET x17 <- #x9 >>> #x8;
        
        (* Concatenate *)
        LET x18 <- {< #x14, #x9, #x17 >};
        
        (* Bitwise Add, unsigned *)
        LET x19 <- #x7 + #x8;
        
        (* Bitwise Mul, unsigned *)
        LET x20 <- #x7 * #x8;
                
        (* Bitwise And *)
        LET x11 <- #x7 .& #x8;
        
        (* Bitwise Or *)
        LET x12 <- #x7 .| #x8;
        
        (* Bitwise Xor *)
        LET x13 <- #x7 .^ #x8;
        
        (* Extract a bit-range *)
        LET x141 <- #x13$[3:4];
        
        (* Extract the LSBits after truncating. Note that the argument to TruncLsb has the LSB size first followed by MSB size *)
        LET x142: Bit 8 <- UniBit (TruncLsb 8 2) #x13;

        (* Extract the MSBits after truncating. Note that the argument to TruncLsb has the LSB size first followed by MSB size *)
        LET x143: Bit 2 <- UniBit (TruncMsb 8 2) #x13;

        (* Expression if-then-else  *)
        LET x21 <- IF !#x3 then #x12 else #x13;
        
        (* Maybe is a STRUCT with 2 values: valid: Bool and data: of a given kind. You can build a struct expression as follows *)
        LET x22 : Maybe (Bit 10) <- STRUCT {
          "valid" ::= #x6 ;
          "data" ::= #x10 } ;
        
        LET x23 <- STRUCT {
          "valid" ::= (!#x6) ;
          "data" ::= (#x10 + #x8) } ;
        
        (* One can have an if-then-else over STRUCTs (and Arrays) *)
        LET x24 <- IF #x3 then #x22 else #x23 ;
        
        (* You can build Arrays *)
        LET x25 : Array 2 Bool <- ARRAY {#x6; #x6 && #x2};
        
        (* Read a field in a struct using @% *)
        LET x26 <- #x23@%"data";

        (* Read an element in an array using @[]. The index should have bit width of exactly ceiling (log2 size of the array) *)
        LET x27 <- #x25@[#x14$[3:3]];

        (* Read an element in an array using constant index. The index is formed using Fin.t values Fin.F1, Fin.FS Fin.F1, etc *)
        LET x28 <- ReadArrayConst #x25 (Fin.F1);
        LET x29 <- ReadArrayConst #x25 (Fin.FS Fin.F1);

        (* An array element can be updated using the following. Here, index x14[2:2] is updated to !x3 *)
        LET x30 <- #x25@[#x14$[3:3] <- !#x3];
        
        (* An struct field can be updated using the following. Here, "valid" is updated to !x3 *)
        LET x31 <- #x23@%["valid" <- !#x3];
        
        (* SignExtend a bit vector *)
        LET _ : Bit 20 <- SignExtend _ #x13;
        
        (* ZeroExtend a bit vector *)
        LET _ : Bit 20 <- ZeroExtend _ #x13;
        
        (* OneExtend a bit vector *)
        LET _ : Bit 20 <- OneExtend _ #x13;

        (* SignExtend or Truncate depending on the sizes *)
        LET _ : Bit 20 <- SignExtendTruncLsb _ #x13;
        
        (* ZeroExtend or Truncate depending on the sizes *)
        LET _ : Bit 20 <- ZeroExtendTruncLsb _ #x13;
        
        (* OneExtend or Truncate depending on the sizes *)
        LET _ : Bit 20 <- OneExtendTruncLsb _ #x13;

        (* To convert a complex type into a bit vector, we can use the pack function *)
        LET x: Bit 11 <- pack #x23 ;
        (* Note that since x23 is a value of type Maybe (Bit 10), the packed value has 11 bits - the 10 bits of data + a valid bit *)
        
        (* To create a value of a complex type back from a bitvector, we can use the unpack function *)
        LET y1: Bit 11 <- $4;
        LET y <- unpack (Maybe (Bit 10)) #y1;

        (* One can create a non-deterministic value of any type. But this can be used only in specification.
          Such a construct cannot generate any circuit *)
        Nondet r1: Bit 11;
        
        (* Sometimes it is useful to write expressions using let-constructs.
          The core Kami does not support let-expressions. Instead it requires you to write actions if let-blocks are needed.
          Actions, however, are non-deterministic. So, if we want to write a simple expression using let-blocks, we use a
          "LetExprSyntax" and convert it to actions using "convertLetExprSyntax_ActionT" as follows: *)
        LETA r2: Bit 10 <- convertLetExprSyntax_ActionT (
          LETC k1: Bit 10 <- #x13 .| #x7;
          LETC k2 <- (#x8 .| #k1);

          (* We can have if-then-else inside let-expressions.
            The predicate is a simple expression, *not* a let-expression *)
          IfE (#k2 == $3)
          then (
            SystemE (
              DispString _ "Hello World\n" ::
              
              DispString _ "Val1 Hex: " ::
              DispHex #x13 ::
              
              nil );
            RetE #k1 )
          else (
            RetE (#k1 + $4))
          as k3;
          
          (* We can omit the else clause and/or the return value in an if-then-else
            just like for actions *)
          IfE (#k2 == #k3)
          then (
            SystemE (
              DispString _ "Bye\n" ::
              nil             
              );
            RetE ($$ (ZToWord 0 0)));
          
          IfE (#k2 == (#k3 + $1))
          then (
            SystemE (
              DispString _ "Bye\n" ::
              nil             
              ) ;
            RetE ($$ (ZToWord 0 0)))
          else (
            SystemE (
              DispString _ "Good Bye\n" ::
              nil             
              ) ;
              RetE ($$ (ZToWord 0 0)));
            
          RetE (#k2 + #k3)
          ) ;
        (* Inside let expressions, you can have let bindings of expressions, system calls (i.e. display statements or finish statements),
          and if-then-else statements *)
        
        Retv)                         
    }.

  (* One can also write modules parameterized by various gallina terms, eg bit-widths etc.
    Sometimes, Coq cannot prove equivalence of various gallina terms,
    in which case you construct the module using the refine tactic as follows.
    In the example below, we have two parameters m and n of type nat. We define two registers
    of type Bit (n+m) and Bit (m+n) and we try to assign from one to the other.
    Since Coq cannot prove (m+n) = (n+m), we use "castBits" to convert the bit vector from one to another.
    The proof itself can be finished using lia.
    *)

  Variable n m : nat.
  Definition exampleModule2: Mod.
    refine (
      MODULE {
        Register @^"reg10": Bit (n + m) <- ($0)%word
        with Register @^"reg11": Bit (m + n) <- ($1)%word
        
        with Rule @^"test" := (
          Read x : Bit (n + m) <- @^"reg10";
          Write @^"reg11" : Bit (m + n) <- castBits _ #x;
          Retv )
        });
    abstract lia.
  Defined.

End exampleModule.

(* Writing ActionT ty *)

(* Tactics *)
