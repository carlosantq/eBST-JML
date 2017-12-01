package main;

import javax.swing.*;
import java.awt.Component;
import java.io.*;

	public class Driver{

		final static /*@ spec_public nullable @*/
		JFileChooser chooser = new JFileChooser();
		static /*@ spec_public nullable @*/
		Component parent = null;
		
		public static void main(String[] args) {
			
			//Ã¡rvore
			No arvore = null;
			int numero = 0;
			String operacao = null;
			int parametro = 0;
			
			//ENTRADA DE ELEMENTOS
			try{
				chooser.setMultiSelectionEnabled(true);
				
				try{
					chooser.showOpenDialog(parent);
				}catch (NullPointerException e){
					System.out.println(e.getStackTrace());
				}
				
				//Abrindo o arquivo passado via argumento
				FileReader fr = null;
				BufferedReader br = null;
				try{
					fr = new FileReader(chooser.getSelectedFile());
					br = new BufferedReader(fr);
				}catch (NullPointerException e){
					System.out.println(e.getStackTrace());
				}
				
				String linha = null;

				//Considerando que apenas uma linha do arquivo serÃ¡ levada em conta
				try{
					 linha = br.readLine();
					 System.out.println("Linha: " + linha);
				}catch (NullPointerException e){
					System.out.println(e.getMessage());
				}
				

				// while (linha != null){
					

					//Primeiro nÃºmero da a raÃ­z da Ã�rvore
					try{
						numero = Integer.parseInt(linha.substring(0, linha.indexOf(" ")));
					}catch (StringIndexOutOfBoundsException e){
						System.out.println(e.getStackTrace());
					}
					
					arvore = new No(numero);

					linha = linha.substring(linha.indexOf(" ")+1, linha.length());

					//Adicionando nÃºmeros do arquivo restantes na Ã¡rvore criada anteriormente
					while (linha.length() > 0){
						numero = Integer.parseInt(linha.substring(0, linha.indexOf(" ")));
						arvore.adicionar(numero);
						linha = linha.substring(linha.indexOf(" ")+1, linha.length());
					}

					// linha = br.readLine();
				// }
				try{
					fr.close();
				}catch (NullPointerException e){
					System.out.println(e.getStackTrace());
				}
			}catch (IOException ioe){
				System.out.println("Erro na abertura do arquivo: " + ioe.getMessage());
			}


			//ENTRADA DE COMANDOS
			try{
				chooser.showOpenDialog(parent);
				FileReader fr;
				BufferedReader br = null;
				try{
					fr = new FileReader(chooser.getSelectedFile());
					br = new BufferedReader(fr);
				}catch (NullPointerException e){
					System.out.println("Erro! Nao foi possivel selecionar o arquivo.");
				}
				
				String linha = null;
				try{
					linha  = br.readLine();
				}catch (NullPointerException e){
					System.out.println("Erro! Nao foi possivel ler a linha atual.");
				}

				while (linha != null){
					//depuracao
					System.out.println("\n> " + linha);

					try{
						operacao = linha.substring(0, linha.indexOf(" "));
					}catch (StringIndexOutOfBoundsException e){
						System.out.println("erro");
					}

					if (operacao.equals("ENESIMO") || operacao.equals("POSICAO") || operacao.equals("REMOVA")){
						linha = linha.substring(linha.indexOf(" ")+1, linha.length());
						parametro = Integer.parseInt(linha.substring(0, linha.length()));
					}

					try{
						switch(operacao){
					
						case "IMPRIMA":
							System.out.println(arvore.toString());
							break;
						case "ENESIMO":
							System.out.println(arvore.enesimoElemento(parametro));
							break;
						case "POSICAO":
							System.out.println(arvore.posicao(parametro));
							break;
						case "REMOVA":
							System.out.println(arvore.remover(parametro) ? "Removido o valor " + parametro : "O valor nao pode ser removido.");
							break;
						case "MEDIANA":
							System.out.println(arvore.mediana());
							break;
						case "CHEIA":
							System.out.println(arvore.ehCheia() ? "Eh Cheia" : "Nao eh cheia");
							break;
						case "COMPLETA":
							System.out.println(arvore.ehCompleta() ? "Eh Completa" : "Nao eh completa");
							break;	
					}

					}catch (NullPointerException e){
						System.out.println("Erro! Nao foi possivel executar esta operacao.");
					}
					try{
						linha = br.readLine();
					}catch(NullPointerException e){
					 	System.out.println("Erro! Nao foi possivel ler a linha atual.");
					 	break;
					}

				}
			}catch (IOException ioe){
				System.out.println("Erro na abertura do arquivo: " + ioe.getMessage());
			}

			System.out.println(arvore.toString());
			arvore.print();
		}
	}
