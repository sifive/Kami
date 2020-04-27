Require Import Kami.Syntax.
Require Import Kami.Notations.
Require Import Kami.LibStruct.

Section lib.

  Record TaggedUnionView := {
    taggedUnionViewTag  : string;
    taggedUnionViewKind : Kind
  }.

  Definition TaggedUnion := list TaggedUnionView.

  Local Definition TagSz (x : TaggedUnion) := Nat.log2_up (length x).

  Local Definition Tag (x : TaggedUnion) := Bit (TagSz x).

  Local Definition list_max (xs : list nat) := fold_left Nat.max xs 0.

  Local Definition DataSz (x : TaggedUnion) :=
    list_max (map (fun view => size (taggedUnionViewKind view)) x).

  Local Definition Data (x : TaggedUnion) := Bit (DataSz x).

  Definition TaggedUnionKind (x : TaggedUnion) :=
    STRUCT_TYPE {
      "tag"  :: Tag x;
      "data" :: Data x
    }.

  Local Definition PackedTaggedUnionKindSz (x : TaggedUnion) := size (TaggedUnionKind x). (* TagSz x + DataSz x + 0. *)

  Definition PackedTaggedUnionKind (x : TaggedUnion) := Bit (PackedTaggedUnionKindSz x).

  Section ty.
    Variable ty : Kind -> Type.

    Definition getTaggedUnionRaw (x : TaggedUnion) (y : PackedTaggedUnionKind x @# ty) :
      TaggedUnionKind x @# ty :=
      unpack (TaggedUnionKind x) y.

    Definition validTag (x : TaggedUnion) (tag : string) : bool :=
      existsb (fun view => String.eqb (taggedUnionViewTag view) tag) x.

    Fixpoint getTaggedUnionKind (x : TaggedUnion) (tag : string) : Kind :=
      match x with
      | [] => Void
      | view :: views =>
        if String.eqb (taggedUnionViewTag view) tag
        then taggedUnionViewKind view
        else getTaggedUnionKind views tag
      end.

    Local Open Scope kami_expr.

    Definition getTaggedUnionDataTypecast (x : TaggedUnion) (tag : string) (data : Data x @# ty) :
      Maybe (getTaggedUnionKind x tag) @# ty :=
      STRUCT {
        "valid" ::= $$(validTag x tag);
        "data"  ::=
          unpack (getTaggedUnionKind x tag)
            (ZeroExtendTruncLsb (size (getTaggedUnionKind x tag)) data)
      }.

    Local Fixpoint getTagIndex (x : TaggedUnion) (tag : string) : option nat :=
      match x with
      | [] => None
      | view :: views =>
        if String.eqb (taggedUnionViewTag view) tag
        then Some 0
        else match getTagIndex views tag with
             | None => None
             | Some n => Some (S n)
             end
      end.

    Definition createTaggedUnion (x : TaggedUnion) (tag : string)
      (y : getTaggedUnionKind x tag @# ty) :
      TaggedUnionKind x @# ty :=
      STRUCT {
        "tag" ::=
          match getTagIndex x tag with
          | None => $0
          | Some n => $n
          end;
        "data" ::= ZeroExtendTruncLsb (DataSz x) (pack y)
      }.

    Local Close Scope kami_expr.

  End ty.

End lib.
