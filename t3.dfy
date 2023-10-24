ghost function toSet(s:seq<int>):set<int>{
  set x | x in s
}

ghost function seqSet(nums:seq<int>, index: nat):set<int>{
  set x | 0 <= x < index <|nums| :: nums[x]
}


class Set {
  var elements: array<int>
  var cont: nat
  ghost var conteudo: seq<int>

  constructor()
    ensures toSet(conteudo) == {}
  {
    elements := new int[0];
    cont := 0;
    conteudo := [];
  }

  ghost predicate SetInvariant()
    reads this, elements
  {
    elements.Length != 0
    && cont <= elements.Length
    && (forall i, j :: 0 <= i < j < cont ==> elements[i] != elements[j])
    && elements[..cont] == conteudo
  }

  method AddElement(x: int) returns (added: bool)
    modifies this, elements
    requires SetInvariant()
    ensures SetInvariant()
    //true se não estava no consunto, false se já estava
    ensures added <==> x !in toSet(old(conteudo))
    //se true, então add "x" ao conjunto (garantindo que os outros elementos não foram perdidos)
    ensures added ==> toSet(old(conteudo)) + {x} == toSet(conteudo)
    //se false, então o conjunto não alterou
    ensures !added ==> toSet(old(conteudo)) == toSet(conteudo)
  {
    var i := 0;
    added := true;
    while i < cont
      invariant 0 <= i <= cont
      invariant SetInvariant()
    {
      if elements[i] == x {
        added := false;
        break;
      }
      i := i + 1;
    }
    if added {
      // Se fizer essa adição em elements o erro SetInvariant() acima possivelmente suma
      //--------------------------------------------------------------------------------------
      //elements := elements + [x];
      var newArr := new int[cont + 1];
      
      var index := 0;
      while index < cont
        invariant 0 <= index <= cont
      {
        newArr[index] := elements[index];
        index := index + 1;
      }

      newArr[cont] := x;
      elements := newArr;
      //--------------------------------------------------------------------------------------
      cont := cont + 1;
      conteudo := conteudo + [x];
    }
  }


  // method RemoveElement(x: int) returns (removed: bool)
  //     requires SetInvariant()
  //     ensures SetInvariant()
  //     ensures removed ==> toSet(old(conteudo)) - {x} == toSet(conteudo)
  //     ensures !removed ==> toSet(old(conteudo)) == toSet(conteudo)
  //   {
  //     var i := 0;
  //     while i < cont
  //       invariant 0 <= i <= cont && SetInvariant()
  //     {
  //       if conteudo[i] == x {
  //         conteudo := conteudo[..i] + conteudo[(i+1)..];
  //         removed := true;
  //       }
  //       i := i + 1;
  //     }
  //     removed := false;
  //   }


  method Contains(x: int) returns (contains: bool)
    requires SetInvariant()
    ensures SetInvariant()
    //ensures contains <==> x in conteudo //este tem nocodigo do sor mas aqui fala que é indufuciente por ão procar um loop
    ensures conteudo == old(conteudo)

  {
    contains := false;
    var i := 0;
    while i < cont
      invariant 0 <= i <= cont
      invariant SetInvariant()
    {
      if elements[i] == x {
        contains := true;
        break;
      }
      i := i + 1;
    }
  }


  method Size() returns (size: nat)
    requires SetInvariant()
    ensures SetInvariant()
    ensures size == cont
  {
    size := cont;
  }


  method IsEmpty() returns (isEmpty: bool)
    requires SetInvariant()
    ensures SetInvariant()
    ensures isEmpty <==> cont == 0
  {
    isEmpty := cont == 0;
  }


  //   method AddAll(nums: array<int>)
  //     requires SetInvariant()
  //     ensures SetInvariant()
  //     ensures toSet(old(conteudo)) + set x | x in nums[..] == toSet(conteudo)
  //   {
  //      for x in nums[..] {
  //        AddElement(x);
  //      }
  //    }
}
