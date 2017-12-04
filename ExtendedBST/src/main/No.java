package main;
import java.util.LinkedList;
import java.util.Queue;

public class No {
	// Atributos
	public int valor;
	
	private /*@ spec_public nullable @*/ No pai;
	private /*@ spec_public nullable @*/ No esq;
	private /*@ spec_public nullable @*/ No dir;
	
	private /*@ spec_public @*/ int nosEsq;
	private /*@ spec_public @*/ int nosDir;
	private /*@ spec_public @*/ int altura;
	
	private /*@ spec_public nullable @*/ Boolean ehCheia;
	private /*@ spec_public nullable @*/ Boolean ehCompleta;
	
	// Construtor
	/*@ 
	  @ assignable pai, esq, dir, nosEsq, nosDir, altura, ehCheia, ehCompleta;
	  @*/
	public No(int valor) {
		this.valor = valor;
		
		pai = null;
		esq = null;
		dir = null;
		
		nosEsq = 0;
		nosDir = 0;
		altura = 0;
		
		ehCheia = true;
		ehCompleta = true;
		
		System.out.println("No criado com o valor " + valor);
	}
	
	// Metodos
	
	// Chamado dentro de adicionar() para corrigir alturas
	/*@ requires altura >= 0;
	  @ assignable altura;
	  @ ensures altura >= \old(altura);
	  @*/
	private void atualizaAltura() {
		if (pai == null) {
			if (esq != null && dir != null) {
				altura = max(esq.altura, dir.altura) + 1;
			}
			else if (esq == null) {
				altura = dir.altura + 1;
			}
			else if (dir == null) {
				altura = esq.altura + 1;
			}
		}
		else {
			if (esq != null && dir != null) {
				altura = max(esq.altura, dir.altura) + 1;
			}
			else if (esq == null) {
				altura = dir.altura + 1;
			}
			else if (dir == null) {
				altura = esq.altura + 1;
			}
			pai.atualizaAltura();
		}
	}
	
	// Retorna o maior de dois numeros
	/*@ assignable \nothing;
	  @ ensures (\result == altura2 && altura2 > altura3) || (\result == altura3 && altura3 >= altura2);
	  @*/
	private /*@ pure @*/ int max(int altura2, int altura3) {
		if (altura2 > altura3) {
			return altura2;
		}
		else {
			return altura3;
		}
	}

	// Atualiza ehCheia
	/*@ assignable ehCheia;
	  @*/
	private void atualizaCheia() {
		
		if (pai == null) {
			// No possui dois filhos
			if (dir != null && esq != null) {
				if (dir.altura == esq.altura && esq.ehCheia && dir.ehCheia) {
					ehCheia = true;
				}
				else {
					ehCheia = false;
				}
			}
			// No possui nenhum filho
			else if (dir == null && esq == null) {
				ehCheia = true;
			}
			// No possui apenas um filho
			else {
				ehCheia = false;
			}
		}
		else {
			// No possui dois filhos
			if (dir != null && esq != null) {
				if (dir.altura == esq.altura && esq.ehCheia && dir.ehCheia) {
					ehCheia = true;
				}
				else {
					ehCheia = false;
				}
			}
			// No possui nenhum filho
			else if (dir == null && esq == null) {
				ehCheia = true;
			}
			// No possui apenas um filho
			else {
				ehCheia = false;
			}
			
			pai.atualizaCheia();
		}
	}
	
	// Checa se o no tem sub-arvores vazias
	/*@ assignable \nothing;
	  @*/
	private /*@ pure @*/ Boolean temSubarvoreVazia() {
		if (esq == null || dir == null) {
			return true;
		}
		else {
			return false;
		}
	}
	
	// Checa se o no tem sub-arvores nao completas
	/*@ assignable \nothing;
	  @*/
	private /*@ pure @*/ Boolean temSubarvoreNaoCompleta() {
		if (!temSubarvoreVazia()) {
			if (esq.ehCompleta && dir.ehCompleta) {
				return false;
			}
			else {
				return true;
			}
		}
		else {
			return false;
		}	
	}
	
	// Atualiza eh ehCompleta
	/*@ assignable ehCompleta;
	  @*/
	private void atualizaCompleta() {
		
		if (pai == null) {
			if ((altura > 1 && temSubarvoreVazia()) || temSubarvoreNaoCompleta()) {
				ehCompleta = false;
			}
			else {
				ehCompleta = true;
			}
		}
		else {
			if (altura > 1 && temSubarvoreVazia()) {
				ehCompleta = false;
			}
			else {
				ehCompleta = true;
			}
			
			pai.atualizaCompleta();
		}
	}
	
	// Corrige nosEsq e nosDir de todo o caminho de insercao em caso de insercao falha
	/*@ assignable this.pai.nosEsq, this.pai.nosDir;
	  @*/
	private void corrigeEsqDir() {
		if (pai != null) {
			if (this == pai.esq) {
				pai.nosEsq--;
				pai.corrigeEsqDir();
			}
			else if (this == pai.dir) {
				pai.nosDir--;
				pai.corrigeEsqDir();
			}
		}
	}
		
	// Adiciona novo elemento a arvore

	public Boolean adicionar(int novoValor) {
		// Novo valor maior que raiz
		if (novoValor > valor) {
			// Achou o lugar para adiciona o novo no
			if (dir == null) {
				// Atualiza numero de nos a direita
				nosDir++;
				
				//Atualiza altura de todo o caminho de insercao
				if (esq == null) {
					altura++;
					if (pai != null) {
						pai.atualizaAltura();
					}
				}
				
				// Adiciona novo no
				dir = new No(novoValor);
				dir.pai = this;
			
				// Atualiza ehCheia de todo o caminho de insercao
				atualizaCheia();
				
				// Atualiza ehCOmpleta de todo o caminho de insercao
				atualizaCompleta();
				
				return true;
			}
			// Nao achou lugar para adicionar o novo no e continua procurando
			else {
				this.nosDir++;
				dir.adicionar(novoValor);
			}
		}
		// Novo valor menor que raiz
		else if (novoValor < valor) {
			// Achou o lugar para adiciona o novo no
			if (esq == null) {
				// Atualiza numero de nos a esquerda
				nosEsq++;
				
				//Atualiza altura de todo o caminho de insercao
				if (dir == null) {
					altura++;
					if (pai != null) {
						pai.atualizaAltura();
					}
				}
				
				// Adiciona novo no
				esq = new No(novoValor);
				esq.pai = this;

				// Atualiza ehCheia de todo o caminho de insercao
				atualizaCheia();
				
				// Atualiza ehCOmpleta de todo o caminho de insercao
				atualizaCompleta();
				
				return true;
			}
			// Nao achou lugar para adicionar o novo no e continua procurando
			else {
				nosEsq++;
				esq.adicionar(novoValor);
			}
		}
		// Novo valor igual a raiz (insercao de valor repetido)
		else {
			this.corrigeEsqDir();
			
			return false;
		}
		
		return false;
	}
	
	// Chamado dentro de remover() para corrigir alturas
	/*@ assignable altura;
	  @*/
	private void atualizaAlturaRemover() {
		if (pai == null) {
			if (esq != null && dir != null) {
				altura = max(esq.altura, dir.altura) + 1;
			}
			else if (esq == null && dir != null) {
				altura = dir.altura + 1;
			}
			else if (dir == null && dir != null) {
				altura = esq.altura + 1;
			}
			else if (esq == null && dir == null) {
				altura = 0;
			}
		}
		else {
			if (esq != null && dir != null) {
				altura = max(esq.altura, dir.altura) + 1;
			}
			else if (esq == null && dir != null) {
				altura = dir.altura + 1;
			}
			else if (dir == null && dir != null) {
				altura = esq.altura + 1;
			}
			else if (esq == null && dir == null) {
				altura = 0;
			}

			pai.atualizaAlturaRemover();
		}
	}
	
	// Corrige nosEsq e nosDir de todo o caminho de remocao em caso e remocao falha
	/*@ assignable this.pai.nosEsq, this.pai.nosDir;
	  @*/
	private void corrigeEsqDirRemover() {
		if (pai != null) {
			if (this == pai.esq) {
				pai.nosEsq++;
				pai.corrigeEsqDirRemover();
			}
			else if (this == pai.dir) {
				pai.nosDir++;
				pai.corrigeEsqDirRemover();
			}
		}
	}
	
	// Remove elemento da arvore
	/*@ requires this != null;
	  @ ensures procurar(valor) == false; @*/
	public Boolean remover(int valor) {
		
		// Chegou a uma folha e nao achou o elemento
		if (this.esq == null && this.dir == null && valor != this.valor) {
			this.corrigeEsqDirRemover();
			
			return false;
		}
		// Procura na sub-arvore direita
		else if (valor > this.valor) {
			nosDir--;
			this.dir.remover(valor);
		}
		// Procura na sub-arvore esquerda
		else if (valor < this.valor) {
			nosEsq--;
			this.esq.remover(valor);
		}
		// Achou o elemento
		else {						
			// Remocao de no folha
			if (esq == null && dir == null) {
				// O no eh filho esquerdo do seu pai
				if (pai.esq == this) {
					pai.esq = null;
					
					pai.atualizaAlturaRemover();
					pai.atualizaCheia();
					pai.atualizaCompleta();
				}
				// O no eh filho direito do seu pai
				else if (pai.dir == this) {
					pai.dir = null;
					
					pai.atualizaAlturaRemover();
					pai.atualizaCheia();
					pai.atualizaCompleta();
				}
				
				return true;
			}
			// Remocao de no com 1 filho a esquerda
			else if (esq != null && dir == null) {
				// O no eh filho esquerdo do seu pai
				if (pai.esq == this) {
					// Troca o filho a esquerda do pai desse no pelo filho a esquerda desse no
					pai.esq = this.esq;
					// Troca o pai do filho a esquerda desse no pelo pai desse no
					this.esq.pai = pai;
					
					pai.atualizaAlturaRemover();
					pai.atualizaCheia();
					pai.atualizaCompleta();
				}
				// O no eh filho direito do seu pai
				else if (pai.dir == this) {
					// Troca o filho a direita do pai desse no pelo filho a esquerda desse no
					pai.dir = this.esq;
					// Troca o pai do filho a esquerda desse no pelo pai desse no
					this.esq.pai = pai;
					
					pai.atualizaAlturaRemover();
					pai.atualizaCheia();
					pai.atualizaCompleta();
				}
				
				return true;
			}
			// Remocao de no com 1 filho a direita
			else if (esq == null && dir != null) {
				// O no eh filho esquerdo do seu pai
				if (pai.esq == this) {
					// Troca o filho a esquerda do pai desse no pelo filho a direita desse no
					pai.esq = this.dir;
					// Troca o pai do filho a direita desse no pelo pai desse no
					this.dir.pai = pai;

					pai.atualizaAlturaRemover();
					pai.atualizaCheia();
					pai.atualizaCompleta();
				}
				// O no eh filho direito do seu pai
				else if (pai.dir == this) {
					// Troca o filho a direita do pai desse no pelo filho a direita desse no
					pai.dir = this.dir;
					// Troca o pai do filho a direita desse no pelo pai desse no
					this.dir.pai = pai;

					pai.atualizaAlturaRemover();
					pai.atualizaCheia();
					pai.atualizaCompleta();
				}
				
				return true;
			}
			
			// Remocao de no com 2 filhos
			else {
				if (pai == null){
					No maior = this.esq.maiorElemento();
					//System.out.println("O maior e: " + maior.valor);

					maior.pai.dir = null;
					maior.pai.atualizaAlturaRemover();
					maior.pai.atualizaCheia();
					maior.pai.atualizaCompleta();
					maior.pai.nosDir-=1;

					this.valor = maior.valor;

					maior.pai = null;
					maior.dir = this.dir;
					maior.esq = this.esq;
					maior.nosEsq = this.nosEsq;
					maior.nosDir = this.nosDir-1;

					maior.atualizaAlturaRemover();
					maior.atualizaCheia();
					maior.atualizaCompleta();
				}

				// O no a ser removido esta na direita, procura o maior elemento da subarvore da esquerda para substituir
				else if (pai.dir == this){
					No maior = this.esq.maiorElemento();
					//System.out.println("O maior e: " + maior.valor);

					maior.pai.dir = null;
					maior.pai.atualizaAlturaRemover();
					maior.pai.atualizaCheia();
					maior.pai.atualizaCompleta();
					maior.pai.nosDir-=1;

					this.pai.dir = maior;
					this.valor = maior.valor;

					maior.pai = this.pai;
					maior.dir = this.dir;
					maior.esq = this.esq;
					maior.nosEsq = this.nosEsq;
					maior.nosDir = this.nosDir-1;

					maior.atualizaAlturaRemover();
					maior.atualizaCheia();
					maior.atualizaCompleta();
				}
				// O no a ser removido esta na esquerda, procura o menor elemento da subarvore da direita para substituir
				else if (pai.esq == this){

					No menor = this.dir.menorElemento();
					//System.out.println("O menor e: " + menor.valor);

					menor.pai.esq = null;
					menor.pai.atualizaAlturaRemover();
					menor.pai.atualizaCheia();
					menor.pai.atualizaCompleta();
					menor.pai.nosEsq-=1;

					this.pai.esq = menor;
					this.valor = menor.valor;

					menor.pai = this.pai;
					menor.esq = this.esq;
					menor.dir = this.dir;
					menor.nosEsq = this.nosEsq-1;
					menor.nosDir = this.nosDir;		
					
					menor.atualizaAlturaRemover();
					menor.atualizaCheia();
					menor.atualizaCompleta();
				}

				return true;
			}
		}
		
		return true;
	}
	
	// Procura o menor elemento de uma arvore
	/*@ requires this != null;
	  @ ensures (\forall int i; 1 <= i && i <= this.nosEsq+this.nosDir+1;
	  			(\result).valor <= enesimoElemento(i) ); @*/
	public /*@ pure @*/ No menorElemento() {
		if (this.esq != null) {
			return this.esq.menorElemento();
		}
		else {
			return this;
		}
	}

	//Procura o maior elemento de uma arvore
	/*@ requires this != null;
	  @ ensures (\forall int i; 1 <= i && i <= this.nosEsq+this.nosDir+1;
	  			(\result).valor >= enesimoElemento(i) ); @*/
	public /*@ pure @*/ No maiorElemento(){
		if (this.dir != null){
			return this.dir.maiorElemento();
		}else{
			return this;
		}
	}
	
	// Procura elemento "valor" na arvore
	/*@ requires this != null;
	  @*/
	public /*@ pure @*/ Boolean procurar(int valor) {
		// Nao achou
		if (valor != this.valor && esq == null && dir == null) {
			return false;
		}
		// Achou
		else if (valor == this.valor) {
			return true;
		}
		// Valor eh maior que raiz
		else if (valor > this.valor) {
			dir.procurar(valor);
		}
		else if (valor < this.valor) {
			esq.procurar(valor);
		}
		
		return false;
	}
	
	// Retorna o elemento na posicao "valor" se a arvore fosse visitada em ordem simetrica
	/*@ requires this != null;
	  @*/
	public /*@ pure @*/ int enesimoElemento(int valor) {
		
		// A posicao do elemento eh igual o numero de elementos a sua esquerda + 1
		int posicao = this.nosEsq + 1;
		
		// Procura na sub-arvore direita
		if (valor > posicao) {
			return dir.enesimoElemento(valor - posicao);
		}
		// Procura na sub-arvore esquerda
		else if (valor < posicao) {
			return esq.enesimoElemento(valor);
		}
		// Achou elemento
		else {
			return this.valor;
		}
	}
	
	// Retorna o numero de posicoes ocupadas pelo ancestral e seus filhos esquerdos
	/*@ requires this != null;
	  @ ensures \result >= 0;
	  @*/
	private /*@ pure @*/ int posicaoDosAncestrais() {
		
		// Se tiver pai
		if (pai != null) {
			// Checa se este elemento eh o filho da direita
			if (pai.dir == this) {
				return pai.posicaoDosAncestrais() + pai.nosEsq + 1;
			}
			// Se nao for elemento da direita nao adiciona nada
			else {
				return pai.posicaoDosAncestrais();
			}
		}
		
		return 0;
	}
	
	// Retorna a posicao do elemento se a arvore fosse visitada em ordem simetrica
	/*@ requires this != null;
	  @ ensures \result >= 1;
	  @*/
	public /*@ pure @*/ int posicao(int elemento) {
		
		// Procura na sub-arvore direita
		if (elemento > this.valor) {
			return dir.posicao(elemento);
		}
		// Procura na sub-arvore esquerda
		else if (elemento < this.valor) {
			return esq.posicao(elemento);
		}
		// Achou o elemento
		else {						
			return nosEsq + 1 + posicaoDosAncestrais();
		}
	}
	
	//Retorna a mediana da arvore
	/*@ requires this != null;
	  @*/
	public int mediana(){

		//Calcula o numero de elementos armazenados na arvore
		int numElementos = this.nosEsq + this.nosDir + 1;
		int mediana;

		if (numElementos % 2 != 0) {
			//Caso o numero de elementos seja um numero impar
			mediana = enesimoElemento((numElementos / 2) + 1);
		}else{
			//Caso o numero de elementos seja um numero par
			mediana = enesimoElemento(numElementos / 2);
		}

		return mediana;
	}
	
	// Retorna true se a arvore for cheia
	/*@ requires this != null;
	  @ ensures \result != null;
	  @*/
	public /*@ pure @*/ Boolean ehCheia() {
		return this.ehCheia;
	}
	
	// Retorna true se a arvore for completa
	/*@ requires this != null;
	  @ ensures \result != null;
	  @*/
	public /*@ pure @*/ Boolean ehCompleta() {
		return this.ehCompleta;
	}
	
	// Retorna a string que representa a arvore numa leitura por nivel
	/*@ also 
	  @ 	requires this != null;
	  @*/
	public String toString() {
		// Fila utilizada no percorrimento em nivel da arvore
		Queue<No> fila = new LinkedList<No>();
		
		// String a ser retornada
		String retorno = "";
		
		// Adiciona raiz a fila
		fila.add(this);
		
		// Enquanto a fila nao esta vazia, enfila os filhos do primeiro elemento
		// da fila e depois concatena o primeiro elemento na string retorno.
		while (!fila.isEmpty()) {
			
			try {
				fila.offer(fila.peek().esq);
			}
			catch (NullPointerException e){}
			
			try {
				fila.offer(fila.peek().dir);
			}
			catch (NullPointerException e){}
			
			try {
				retorno = retorno + fila.peek().valor + " ";
			}
			catch (NullPointerException e){}
			
			fila.poll();
		}
		// Apaga o ultimo espaco
		retorno = retorno.substring(0, retorno.length()-1);
		
		return retorno;
	}

	// Imprime todos os elementos da arvore em pre-ordem detalhando seus atributos
	/*@ requires this != null;
	  @*/
	public /*@ pure @*/ void print () {
		System.out.println("> No: " + this.valor);
		
		if (this.pai != null) {
			System.out.println("\tPai: " + this.pai.valor);
		}
		else {
			System.out.println("\tPai: null");
		}
		
		if (this.esq != null) {
			System.out.println("\tFilho esquerdo: " + this.esq.valor);
		}
		else {
			System.out.println("\tFilho esquerdo: null");
		}
		if (this.dir != null) {
			System.out.println("\tFilho direito " + this.dir.valor);
		}
		else {
			System.out.println("\tFilho direito: null");
		}
		
		System.out.println("\tAltura: " + this.altura);
		
		System.out.println("\tNos a esquerda: " + this.nosEsq);
		System.out.println("\tNos a direita: " + this.nosDir);
		System.out.println("\tehCheia: " + this.ehCheia);
		System.out.println("\tehCompl: " + this.ehCompleta);
		
		if (esq != null) {
			esq.print();
		}
		if (dir != null) {
			dir.print();
		}

	}
}
