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

  method Add(x: int) returns (added: bool)
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
      var newArr := new int[cont + 1];
      
      var i := 0;
      var j := 0;
      while i < elements.Length
        invariant 0 <= j < newArr.Length
        invariant 0 <= i < elements.Length
      assert 0 <= j < newArr.Length;
      assert 0 <= i < elements.Length;
      {
        newArr[j] := elements[i];
        i := i + 1;
        j := j +1;
      }

      newArr[newArr.Length - 1] := x;
      elements := newArr;
      cont := cont + 1;
      conteudo := conteudo + [x];
    }
  }


//  method Remove(x: int) returns (removed: bool)
//   modifies this, elements
//   requires SetInvariant()
//   ensures SetInvariant()
//   //true se não estava no consunto, false se já estava
//   //ensures removed <==> x !in toSet(old(conteudo))
//   //ensures removed ==> toSet(old(conteudo)) - {x} == toSet(conteudo)
//   ensures !removed ==> toSet(old(conteudo)) == toSet(conteudo)
// {
//   removed := false;
//   var i := 0;
//   while i < cont
//     invariant 0 <= i <= cont
//     invariant SetInvariant()
//   {
//     if elements[i] == x {
//       conteudo := conteudo[..i] + conteudo[(i+1)..];
//       removed := true;
//       break;
//     }
//     i := i + 1;
//   }

//   if removed {
//     var newArr := new int[cont - 1];
//     var j := 0;
//     for i := 0 to cont - 1 
//       invariant 0 <= j <= cont - 1
//       invariant 0 <= i <= cont - 1
//     {
//       if elements[i] != x {
//         newArr[j] := elements[i];
//         j := j + 1;
//       }
//     }
//     elements := newArr;
//     cont := cont - 1;
//   }
// }



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


method AddAll(nums: array<int>)
  requires SetInvariant()
  modifies this, elements
  ensures SetInvariant()
  ensures toSet(old(conteudo)) + toSet(nums[..]) == toSet(conteudo)
{
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant SetInvariant()
    invariant toSet(old(conteudo)) + seqSet(nums[..], i) == toSet(conteudo)
    decreases nums.Length - i
  {
    var newArr := new int[cont + 1];
      
      var i := 0;
      var j := 0;
      while i < elements.Length
        invariant 0 <= j < newArr.Length
        invariant 0 <= i < elements.Length
      assert 0 <= j < newArr.Length;
      assert 0 <= i < elements.Length;
      {
        newArr[j] := elements[i];
        i := i + 1;
        j := j +1;
      }

      newArr[newArr.Length - 1] := nums[i];
      elements := newArr;
      cont := cont + 1;
      conteudo := conteudo + [nums[i]];
    i := i + 1;
  }
}
}
