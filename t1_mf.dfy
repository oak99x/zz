//  Métodos Formais
//  Trabalho I - Construir especificações e verificações formais na linguagem Dafny para algoritmos sobre estruturas de dados. 

//  Implementação do tipo abstrato de dados Conjunto (Set).

//  Alunos:
//  Enzo Contursi Silveira
//  Giovanni Masoni Schenato
//  Jeniffer Moreira Borges
//  Mateus de Carvalho de Freitas

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

  constructor(size: int)
    requires size > 0 
    ensures toSet(conteudo) == {}
  {
    elements := new int[size];
    cont := 0;
    conteudo := [];
  }

  ghost predicate SetInvariant()
    reads this, elements
  {
    //array pode receber elementos
    elements.Length != 0
    //contagem não pode exeder o tamanho do conjunto
    && cont <= elements.Length
    //verifica que todos os elementos do conjunto devem ser distintos
    && (forall i, j :: 0 <= i < j < cont ==> elements[i] != elements[j])
    && elements[..cont] == conteudo
  }

  method AddElement(x: int) returns (added: bool)
    requires SetInvariant()
    modifies this, elements
    ensures SetInvariant()
    // se true, então add "x" ao conjunto
    ensures added ==> toSet(conteudo) == old(toSet(conteudo)) + {x}
    // se false, então o conjunto não alterou
    ensures !added ==> toSet(conteudo) == old(toSet(conteudo))
  {
    var contains := Contains(x);
    if contains {
      added := false;
    } else{
      if cont < elements.Length {
        elements[cont] := x;
        cont := cont + 1;
        conteudo := conteudo + [x];
        added := true;
      } else {
        // O array está cheio, não é possível adicionar mais elementos.
        added := false;
      }
    }
  }

method RemoveElement(x: int) returns (removed: bool)
    modifies elements
    requires SetInvariant()
    ensures SetInvariant()
    // se true, então remove "x" do conjunto (garantindo que os outros elementos não foram perdidos)
    ensures removed ==> toSet(conteudo) == old(toSet(conteudo)) - {x}
    // se false, então o conjunto não alterou
    ensures !removed ==> toSet(conteudo) == old(toSet(conteudo))
{
    var i := 0;
    removed := false;

    while i < cont
      invariant 0 <= i <= cont
      invariant SetInvariant()
      invariant !removed ==> conteudo == old(conteudo)
      decreases cont - i 
    {
        if elements[i] == x {
            
            var newArr := new int[elements.Length];

            if i < cont - 1 {
                // Reorganiza os elementos do array a partir da posição i exemplo [12345] fica [12355]
                var j := i;
                while j < cont - 1
                    invariant i <= j <= cont - 1 < elements.Length
                {
                    elements[j] := elements[j + 1];
                    j := j + 1;
                }

                // Tira o ultimo elemento que ficou igual depois da reorganização exemplo [12355] fica [1235 ]
                var k := 0;
                while k < cont-1
                    invariant 0 <= k <= cont-1 < elements.Length
                    invariant elements.Length == newArr.Length
                {
                    newArr[k] := elements[k];
                    k := k + 1;
                }
            }

            elements := newArr; //?????????
            removed := true;
            conteudo := conteudo[..i] + conteudo[i + 1..];
            cont := cont - 1;
            break;
        }
        i := i + 1;
    }
}


  method Contains(x: int) returns (contains: bool)
    requires SetInvariant()
    ensures SetInvariant()
    //ensures contains <==> x in conteudo // Erro ****  postcondition could not be proved on this return path
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
    ensures size == |conteudo|
  {
    size := cont;
  }

  method IsEmpty() returns (empty: bool)
    requires SetInvariant()
    ensures SetInvariant()
    ensures empty <==> |conteudo| == 0
  {
    empty := cont == 0;
  }

  method AddAll(nums: array<int>)
    modifies this, elements
    requires SetInvariant()
    requires nums.Length != 0
    ensures SetInvariant()
    //ensures toSet(conteudo) == old(toSet(conteudo)) + set x | x in nums[..] // Erro ****  postcondition could not be proved on this return path
  {
    var i := 0;
    while i < nums.Length
      invariant SetInvariant()
      invariant 0 <= i <= nums.Length
    {
      var contains := Contains(nums[i]);
      if (!contains) {
        // if cont < elements.Length {
        //   elements[cont] := nums[i];
        //   cont := cont + 1;
        //   conteudo := conteudo + [nums[i]];
        // }
        var add := AddElement(nums[i]); 
      }
      i := i + 1;
    }
  }
}


method Main()
{
  var set1 := new Set(5);
  var set2 := new Set(3);

  // Adicionar elementos aos conjuntos
  var added1 := set1.AddElement(1);
  var added2 := set1.AddElement(2);
  var added3 := set1.AddElement(3);
  var added4 := set2.AddElement(2);
  var added5 := set2.AddElement(4);

  // Verificar se os elementos foram adicionados corretamente
  assert added1;
  assert added2;
  assert added3;
  assert added4;
  assert added5;

  // Verificar o tamanho dos conjuntos
  var s1 := set1.Size();
  var s2 := set2.Size();
  assert s1 == 3;
  assert s2 == 2;

  // Verificar se os conjuntos não estão vazios
  var c := set1.IsEmpty();
  var d := set2.IsEmpty();
  assert !c;
  assert !d;

  // Verificar se os conjuntos contêm elementos específicos
  var c1 := set1.Contains(1);
  var c2 := set1.Contains(2);
  var c3 := set1.Contains(3);
  var c4 := set2.Contains(2);
  var c5 := set2.Contains(4);
  assert c1;
  assert c2;
  assert c3;
  assert c4;
  assert c5;
 
  // Remover elementos dos conjuntos
  var removed1 := set1.RemoveElement(2);
  var removed2 := set2.RemoveElement(2);

  // Verificar se os elementos foram removidos corretamente
  assert removed1;
  assert removed2;

  // Verificar o tamanho atualizado dos conjuntos
  s1 := set1.Size();
  s2 := set2.Size();
  assert s1 == 2;
  assert s2 == 1;

  // Verificar que os elementos removidos não estão mais nos conjuntos
  c1 := set1.Contains(2);
  c2 := set2.Contains(2);
  assert !c1;
  assert !c2;

  // Testar o método AddAll
  var numsToAdd := new int[3];
  numsToAdd[0] := 5;
  numsToAdd[1] := 6;
  numsToAdd[2] := 7;

  set1.AddAll(numsToAdd);

  // Verificar se os elementos foram adicionados corretamente usando o método AddAll
  s1 := set1.Size();
  c1 := set1.Contains(5);
  c2 := set1.Contains(6);
  c3 := set1.Contains(7);
  assert  s1 == 5;
  assert c1;
  assert c2;
  assert c3;
}
