Require Export Bool Ascii String Fin List FunctionalExtensionality Psatz PeanoNat.
Require Export Kami.Syntax.

Print ActionT.
Print Kind.
Print fullType.
Print unit.
Print tt.
Check tt.

Fixpoint WfActionT_unit {k} (regs : list (string * {x : FullKind & RegInitValT x})) (a : ActionT (fun _ => unit) k) : bool :=
                             match a with
                             | MCall meth s e cont => WfActionT_unit regs (cont tt)
                             | LetExpr k' e cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                   | SyntaxKind k'' => fun cont => WfActionT_unit regs (cont tt)
                                                   | @NativeKind k'' v => fun cont => false
                                                   end cont
                             | LetAction k a cont => WfActionT_unit regs a && WfActionT_unit regs (cont tt)
                             | ReadNondet k' cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                    | SyntaxKind k'' => fun cont => WfActionT_unit regs (cont tt)
                                                    | @NativeKind k'' v => fun cont => false
                                                    end cont
                             | ReadReg r k' cont => match lookup String.eqb r regs with
                                                    | None => false
                                                    | Some (existT k'' _) =>
                                                      match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                      | SyntaxKind k''' => match k'' with
                                                                           | SyntaxKind k'''' => fun cont => Kind_decb k''' k'''' && WfActionT_unit regs (cont tt)
                                                                           | @NativeKind k'''' v => fun cont => false
                                                                           end
                                                      | @NativeKind k''' v => fun cont => false
                                                      end cont
                                                   end
                             | WriteReg r k' e cont => match lookup String.eqb r regs with
                                                     | None => false
                                                     | Some (existT k'' _) =>
                                                        match k',k'' with
                                                        | SyntaxKind k''',SyntaxKind k'''' => Kind_decb k''' k'''' && WfActionT_unit regs cont
                                                        | _,_ => false
                                                        end
                                                     end
                             | IfElse cond k' atrue afalse cont => (WfActionT_unit regs atrue) && (WfActionT_unit regs afalse) && (WfActionT_unit regs (cont tt))
                             | Sys l cont => WfActionT_unit regs cont
                             | Return e => true
                             (*| _ => false*)
                             end.

Fixpoint has_native {k} (a : ActionT (fun _ => unit) k) : bool :=
                         match a with
                         | MCall meth s e cont => false
                         | LetExpr k' e cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                | SyntaxKind k'' => fun cont => has_native (cont tt)
                                                | @NativeKind k'' v => fun cont => true
                                                end cont
                         | LetAction k a cont => has_native a && has_native (cont tt)
                         | ReadNondet k' cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                 | SyntaxKind k'' => fun cont => has_native (cont tt)
                                                 | @NativeKind k'' v => fun cont => true
                                                 end cont
                         | ReadReg r k' cont => match k' return (fullType (fun _ => unit) k' -> ActionT (fun _ => unit) k) -> bool with
                                                | SyntaxKind k''' => fun cont => has_native (cont tt)
                                                | @NativeKind k''' v => fun cont => true
                                                end cont
                         | WriteReg r k' e cont => match k' with
                                                   | SyntaxKind k'' => has_native cont
                                                   | _ => true
                                                   end
                         | IfElse cond k' atrue afalse cont => (has_native atrue) && (has_native afalse) && (has_native (cont tt))
                         | Sys l cont => has_native cont
                         | Return e => false
                         (*| _ => false*)
                         end.
                        

Theorem test: forall regs k (a:ActionT (fun _ => unit) k), (WfActionT_unit regs a && negb(has_native a))=true -> @WfActionT_new regs (fun _ => unit) k a.
Admitted.

Axiom test2: forall regs k (a:forall ty k, ActionT ty k), @WfActionT_new regs (fun _ => unit) k (a (fun _ => unit) k) ->
                                                          forall ty k, @WfActionT_new regs ty k (a ty k).

