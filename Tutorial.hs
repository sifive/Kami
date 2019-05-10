module Tutorial where

import qualified Prelude
import qualified String
import qualified Syntax
import qualified Word

coq_IncrementerImpl :: Prelude.String -> Syntax.BaseModule
coq_IncrementerImpl name =
  Syntax.makeModule (Syntax.ConsInModule (Syntax.MERegister ((,)
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'c' ((:) 'o' ((:) 'u' ((:) 'n' ((:)
        't' ((:) 'e' ((:) 'r' ([])))))))))) ((,) (Syntax.SyntaxKind
    (Syntax.Bit (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))))) (Prelude.Just
    (Syntax.makeConst (Syntax.Bit (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ 0))))))
      (Syntax.getDefaultConst (Syntax.Bit (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))))
    (Syntax.ConsInModule (Syntax.MERegister ((,)
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'c' ((:) 'o' ((:) 'u' ((:) 'n' ((:)
        't' ((:) 'e' ((:) 'r' ((:) '1' ([]))))))))))) ((,) (Syntax.SyntaxKind
    (Syntax.Bit (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))))) (Prelude.Just
    (Syntax.makeConst (Syntax.Bit (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ (Prelude.succ 0))))))
      (Syntax.getDefaultConst (Syntax.Bit (Prelude.succ (Prelude.succ
        (Prelude.succ (Prelude.succ (Prelude.succ 0))))))))))))
    (Syntax.ConsInModule (Syntax.MERegister ((,)
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'i' ((:) 's' ((:) 'S' ((:) 'e' ((:)
        'n' ((:) 'd' ((:) 'i' ((:) 'n' ((:) 'g' ([])))))))))))) ((,)
    (Syntax.SyntaxKind Syntax.Bool) (Prelude.Just
    (Syntax.makeConst Syntax.Bool (Syntax.ConstBool Prelude.True))))))
    (Syntax.ConsInModule (Syntax.MERule ((,)
    (String.append name
      (String.append ((:) '.' ([])) ((:) 's' ((:) 'e' ((:) 'n' ((:) 'd'
        ([]))))))) (\_ -> Syntax.ReadReg
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'i' ((:) 's' ((:) 'S' ((:) 'e' ((:)
        'n' ((:) 'd' ((:) 'i' ((:) 'n' ((:) 'g' ([]))))))))))))
    (Syntax.SyntaxKind Syntax.Bool) (\isSending -> Syntax.Assertion
    (Syntax.Var (Syntax.SyntaxKind Syntax.Bool) isSending) (Syntax.ReadReg
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'c' ((:) 'o' ((:) 'u' ((:) 'n' ((:)
        't' ((:) 'e' ((:) 'r' ([])))))))))) (Syntax.SyntaxKind (Syntax.Bit
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    0))))))) (\counter -> Syntax.MCall ((:) 'c' ((:) 'o' ((:) 'u' ((:) 'n'
    ((:) 't' ((:) 'e' ((:) 'r' ((:) 'V' ((:) 'a' ((:) 'l' ([]))))))))))) ((,)
    (Syntax.Bit (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0)))))) (Syntax.Bit 0)) (Syntax.Var (Syntax.SyntaxKind
    (Syntax.Bit (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))))) counter) (\_ -> Syntax.WriteReg
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'i' ((:) 's' ((:) 'S' ((:) 'e' ((:)
        'n' ((:) 'd' ((:) 'i' ((:) 'n' ((:) 'g' ([]))))))))))))
    (Syntax.SyntaxKind Syntax.Bool) (Syntax.UniBool Syntax.Neg (Syntax.Var
    (Syntax.SyntaxKind Syntax.Bool) isSending)) (Syntax.Return (Syntax.Const
    (Syntax.Bit 0) (Syntax.getDefaultConst (Syntax.Bit 0)))))))))))
    (Syntax.ConsInModule (Syntax.MERule ((,)
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'i' ((:) 'n' ((:) 'c' ([]))))))
    (\_ -> Syntax.ReadReg
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'i' ((:) 's' ((:) 'S' ((:) 'e' ((:)
        'n' ((:) 'd' ((:) 'i' ((:) 'n' ((:) 'g' ([]))))))))))))
    (Syntax.SyntaxKind Syntax.Bool) (\isSending -> Syntax.Assertion
    (Syntax.UniBool Syntax.Neg (Syntax.Var (Syntax.SyntaxKind Syntax.Bool)
    isSending)) (Syntax.ReadReg
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'c' ((:) 'o' ((:) 'u' ((:) 'n' ((:)
        't' ((:) 'e' ((:) 'r' ([])))))))))) (Syntax.SyntaxKind (Syntax.Bit
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    0))))))) (\counter -> Syntax.WriteReg
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'c' ((:) 'o' ((:) 'u' ((:) 'n' ((:)
        't' ((:) 'e' ((:) 'r' ([])))))))))) (Syntax.SyntaxKind (Syntax.Bit
    (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    0))))))) (Syntax.CABit (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ 0))))) Syntax.Add ((:) (Syntax.Var
    (Syntax.SyntaxKind (Syntax.Bit (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ 0))))))) counter) ((:) (Syntax.Const
    (Syntax.Bit (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    (Prelude.succ 0)))))) (Syntax.ConstBit (Prelude.succ (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ 0)))))
    (Word.natToWord (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
      (Prelude.succ 0))))) (Prelude.succ 0)))) ([])))) (Syntax.WriteReg
    (String.append name
      (String.append ((:) '.' ([])) ((:) 'i' ((:) 's' ((:) 'S' ((:) 'e' ((:)
        'n' ((:) 'd' ((:) 'i' ((:) 'n' ((:) 'g' ([]))))))))))))
    (Syntax.SyntaxKind Syntax.Bool) (Syntax.UniBool Syntax.Neg (Syntax.Var
    (Syntax.SyntaxKind Syntax.Bool) isSending)) (Syntax.Return (Syntax.Const
    (Syntax.Bit 0) (Syntax.getDefaultConst (Syntax.Bit 0)))))))))))
    Syntax.NilInModule)))))

