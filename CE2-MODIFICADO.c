/*
Programa de demonstracao de analise nodal modificada
Por Antonio Carlos M. de Queiroz acmq@coe.ufrj.br
Versao 1.0 - 6/9/2000
Versao 1.0a - 8/9/2000 Ignora comentarios
Versao 1.0b - 15/9/2000 Aumentado Yn, retirado Js
Versao 1.0c - 19/2/2001 Mais comentarios
Versao 1.0d - 16/2/2003 Tratamento correto de nomes em minusculas
Versao 1.0e - 21/8/2008 Estampas sempre somam. Ignora a primeira linha
Versao 1.0f - 21/6/2009 Corrigidos limites de alocacao de Yn
Versao 1.0g - 15/10/2009 Le as linhas inteiras
Versao 1.0h - 18/6/2011 Estampas correspondendo a modelos
Versao 1.0i - 03/11/2013 Correcoes em *p e saida com sistema singular.
Versao 1.0j - 26/11/2015 Evita operacoes com zero.
Versao 1.0k - 23/06/2016 Calcula P.O. com L, C e K (o acoplamento é ignorado, pois P.O. é análise DC)
Versao 1.0l - 24/06/2016 Leitura do netlist para elemento MOS 
Versao 1.0m - 27/06/2016 Tensões iniciais aleatórias atribuídas (para NP) e verificação dos 3 modos de operação dos MOS 
Versao 1.0n - 03/07/2016 Linearização dos transistores MOS para valores iniciais. Criação da função verMOSCond(). Falta resolver I0
Versao 1.0o - 06/07/2016 I0 "supostamente" resolvido
Versao 1.0p - 09/07/1016 Newton-Raphson implementado(by fefa), porém, os circuitos com elementos MOS não convergem....
*/

/*
Elementos aceitos e linhas do netlist:
Resistor:      R<nome> <no+> <no-> <resistencia>
Indutor:       L<nome> <nó+> <nó-> <indutancia>
Acoplamento:   K<nome> <LA> <LB> <k> (indutores LA e LB já declarados)
Capacitor:     C<nome> <nó+> <nó-> <capacitancia>
VCCS:          G<nome> <io+> <io-> <vi+> <vi-> <transcondutancia>
VCVC:          E<nome> <vo+> <vo-> <vi+> <vi-> <ganho de tensao>
CCCS:          F<nome> <io+> <io-> <ii+> <ii-> <ganho de corrente>
CCVS:          H<nome> <vo+> <vo-> <ii+> <ii-> <transresistencia>
Fonte I:       I<nome> <io+> <io-> <corrente>
Fonte V:       V<nome> <vo+> <vo-> <tensao>
Amp. op.:      O<nome> <vo1> <vo2> <vi1> <vi2>
TransistorMOS: M<nome> <nód> <nóg> <nós> <nób> <NMOS ou PMOS> L=<comprimento> W=<largura> <K> <Vt0> <lambda> <gama> <phi> <Ld>
As fontes F e H tem o ramo de entrada em curto
O amplificador operacional ideal tem a saida suspensa
Os nos podem ser nomes
*/

//Trabalho de Circuitos Elétricos 2 - 
#define versao "1.0 - 14/07/2016"
#include <stdio.h>
#include <conio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <math.h>
#include <complex.h>
#include <time.h>
#define MAX_LINHA 80
#define MAX_NOME 11
#define MAX_ELEM 500
#define MAX_NOS 50
#define TOLG 1e-50
#define PI 3.14159265358979
#define UM 0.999999999999999999999999999999999999999999 //utilizado para tratar os erros numericos no seno e cosseno
#define ZERO 0.0000000000000000000000000000000000000001 //utilizado para tratar os erros numericos no seno e cosseno
#define DEBUG

typedef struct elemento { /* Elemento do netlist */
  char nome[MAX_NOME],tipo[MAX_NOME],modo[MAX_NOME];
  double valor,modulo,fase;
  int a,b,c,d,x,y;
  double gm,gmb,rgds,i0,ids,cbg,cgs,cgd;
  int invertido;
} elemento;

elemento netlist[MAX_ELEM]; /* Netlist */

typedef struct acoplamento {
  char lA[MAX_NOME],lB[MAX_NOME];
} acoplamento;

acoplamento acop_K[MAX_ELEM];

typedef struct transitorMOS {
   char tipo[MAX_NOME],modo[MAX_NOME];
   double cp,lg,transK,vt0,lambda,gama,phi,ld,cox,
   		  vd[2],vg[2],vs[2],vb[2],vt[2],
          cgs,cgd,cbg,
		  rgds,gm,gmb,ids,i0;
   int invertido;
} transistorMOS;

transistorMOS mos[MAX_ELEM];

double ind_L[MAX_ELEM], cap_C[MAX_ELEM], ind_M, valorLA, valorLB; /*guarda os valores de indutancia e capacitancia p/ serem utilizados no modelo de peq. sinais*/ 

int
  ne, /* Elementos */
  nv, /* Variaveis */
  nn, /* Nos */
  i,j,k, indice,n,
  inc_L, inc_C, tensaoMOS[MAX_ELEM][4],/*tensaoMOS[]: vínculo entre nó e tensão (não confundir com valor de tensão!)*/
  ne_extra,linear;
  
short fim = 0, contadorMos = 0;
int   contador =1,tem, convergencia[MAX_ELEM][4];

char
/* Foram colocados limites nos formatos de leitura para alguma protecao
   contra excesso de caracteres nestas variaveis */
  nomearquivo[MAX_LINHA+1],novonome[MAX_LINHA+1],
  tipo,escala[3],
  na[MAX_NOME],nb[MAX_NOME],nc[MAX_NOME],nd[MAX_NOME],
  lista[MAX_NOS+1][MAX_NOME+2], /*Tem que caber jx antes do nome */
  txt[MAX_LINHA+1],
  *p;
FILE *arquivo;

double
  g,aux,freqInicial,freqFinal,frequencia,pontos,passo,vds,vgs,vbs,vt,
  Yn[MAX_NOS+1][MAX_NOS+2];        //matriz nodal
  
double complex 
    gComplex, amplitude, fase,
    YnComplex[MAX_NOS+1][MAX_NOS+2];  //matriz nodal com complexos (análise da resposta em frequencia)

double sind (double ang)
{
    double t = sin( (ang / 180.0) * PI );
    if (t > UM)
        return (1.0);
    if (t < -UM)
        return (-1.0);
    if (fabs(t) < ZERO)
        return (0.0);

    return (t);
}

double cosd (double ang)
{
    double t = cos( (ang / 180.0) * PI );
    if (t > UM)
        return (1.0);
    if ( t < -UM)
        return (-1.0);
    if (fabs(t) < ZERO)
        return (0.0);

    return cos( (ang / 180.0) * PI );
}

void trocaNome(){ //rotina que troca extensao de .net para .tab
	do {n++;} while(nomearquivo[n]!='.');
	memcpy(novonome, &nomearquivo[0],n);
    novonome[n]='\0';
	strcpy(novonome,strcat(novonome,".tab"));
	printf("\nResultados escritos no arquivo %s",novonome);
}

void verMOSCond(void){
 //verifica as tensões do transistor MOS e calcula adequadamente as condutâncias linearizadas
	mos[linear].invertido=0;
   if(mos[linear].vd[0]>=mos[linear].vs[0]){
    	if(mos[linear].vd[0]=mos[linear].vs[0]){
      	mos[linear].vd[0]+=1e-3;
    }
    if(mos[linear].tipo[0]=='N' || mos[linear].tipo[0]=='P'){
      //VERIFICA INVERSAO
      if(mos[linear].tipo[0]=='P'){
        mos[linear].invertido=1;
        aux=mos[linear].vd[0];
        mos[linear].vd[0]=mos[linear].vs[0];
        mos[linear].vs[0]=aux;  
      }
      //CORTE
      if((mos[linear].vg[0]-mos[linear].vs[0])<mos[linear].vt[0]){       
    	mos[linear].cgs=mos[linear].cox*mos[linear].cp*mos[linear].ld;
        mos[linear].cgd=mos[linear].cgs;
        mos[linear].cbg=mos[linear].cox*mos[linear].cp*mos[linear].lg;
        strcpy(mos[linear].modo,"CORTE");
      }
        //TRIODO
      else if((mos[linear].vd[0]-mos[linear].vs[0])<=(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])){         
        mos[linear]	.cgs=mos[linear].cox*mos[linear].cp*mos[linear].ld+(mos[linear].cox*mos[linear].cp*mos[linear].lg)/2;
        mos[linear].cgd=mos[linear].cgs;
        mos[linear].cbg=0;        
        mos[linear].rgds = ((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])-2*(mos[linear].vd[0]-mos[linear].vs[0])+4*mos[linear].lambda*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(mos[linear].vd[0]-mos[linear].vs[0])-3*mos[linear].lambda*(mos[linear].vd[0]-mos[linear].vs[0])*(mos[linear].vd[0]-mos[linear].vs[0])));
        mos[linear].gm = ((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vd[0]-mos[linear].vs[0])*(1+mos[linear].lambda*(mos[linear].vd[0]-mos[linear].vs[0]))));
        mos[linear].gmb = ((((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vd[0]-mos[linear].vs[0])*(1+mos[linear].lambda*(mos[linear].vd[0]-mos[linear].vs[0]))))*mos[linear].gama)/(sqrt(mos[linear].phi-mos[linear].vb[0]+mos[linear].vs[0])));       
        mos[linear].ids = ((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(mos[linear].vd[0]-mos[linear].vs[0])-(mos[linear].vd[0]-mos[linear].vs[0])*(mos[linear].vd[0]-mos[linear].vs[0]))*(1+mos[linear].lambda*(mos[linear].vd[0]-mos[linear].vs[0])));
        //I0 = id - Gm*vgs - Gmb*vbs - Gds*vds
        mos[linear].i0 = mos[linear].ids - mos[linear].gm*(mos[linear].vg[0]-mos[linear].vs[0]) - mos[linear].gmb*(mos[linear].vb[0]-mos[linear].vs[0]) - mos[linear].rgds*(mos[linear].vd[0]-mos[linear].vs[0]);
        strcpy(mos[linear].modo,"TRIODO");
	  }
      
      //SATURACAO
      else if((mos[linear].vd[0]-mos[linear].vs[0])>(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])){         
    	mos[linear].cgs=mos[linear].cox*mos[linear].cp*mos[linear].ld+2*(mos[linear].cox*mos[linear].cp*mos[linear].lg)/3;
        mos[linear].cgd=mos[linear].cox*mos[linear].cp*mos[linear].ld;
        mos[linear].cbg=0;
    	mos[linear].rgds = ((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*mos[linear].lambda);
        mos[linear].gm = ((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(1+mos[linear].lambda*(mos[linear].vd[0]-mos[linear].vs[0]))));
        mos[linear].gmb = ((((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(1+mos[linear].lambda*(mos[linear].vd[0]-mos[linear].vs[0]))))*mos[linear].gama)/(sqrt(mos[linear].phi-mos[linear].vb[0]+mos[linear].vs[0])));
        mos[linear].ids = (mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(1+mos[linear].lambda*(mos[linear].vd[0]-mos[linear].vs[0]));
     	//I0 = id - Gm*vgs - Gmb*vbs - Gds*vds
        mos[linear].i0 = mos[linear].ids - mos[linear].gm*(mos[linear].vg[0]-mos[linear].vs[0]) - mos[linear].gmb*(mos[linear].vb[0]-mos[linear].vs[0]) - mos[linear].rgds*(mos[linear].vd[0]-mos[linear].vs[0]);
        strcpy(mos[linear].modo,"SATURACAO");
	  }
    }    
  }
  else if(mos[linear].vd[0]<mos[linear].vs[0]){    
    if(mos[linear].tipo[0]=='P' || mos[linear].tipo[0]=='N'){
      //inverte vd com vs
      if(mos[linear].tipo[0]=='N'){
        mos[linear].invertido=1;
        aux=mos[linear].vd[0];
        mos[linear].vd[0]=mos[linear].vs[0];
        mos[linear].vs[0]=aux;  
      }      
      //CORTE
      if((mos[linear].vg[0]-mos[linear].vs[0])<mos[linear].vt[0]){        
    	mos[linear].cgs=mos[linear].cox*mos[linear].cp*mos[linear].ld;
        mos[linear].cgd=mos[linear].cgs;
        mos[linear].cbg=mos[linear].cox*mos[linear].cp*mos[linear].lg;
        strcpy(mos[linear].modo,"CORTE");
      }
        //TRIODO
      else if((mos[linear].vd[0]-mos[linear].vs[0])>=(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])){        
        mos[linear].cgs=mos[linear].cox*mos[linear].cp*mos[linear].ld+(mos[linear].cox*mos[linear].cp*mos[linear].lg)/2;
        mos[linear].cgd=mos[linear].cgs;
        mos[linear].cbg=0;
        mos[linear].rgds = ((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vs[0]-mos[linear].vg[0]+mos[linear].vt[0])-2*(mos[linear].vs[0]-mos[linear].vd[0])+4*mos[linear].lambda*(mos[linear].vs[0]-mos[linear].vg[0]+mos[linear].vt[0])*(mos[linear].vs[0]-mos[linear].vd[0])-3*mos[linear].lambda*(mos[linear].vs[0]-mos[linear].vd[0])*(mos[linear].vs[0]-mos[linear].vd[0])));
        mos[linear].gm  = ((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vs[0]-mos[linear].vd[0])*(1+mos[linear].lambda*(mos[linear].vs[0]-mos[linear].vd[0]))));
        mos[linear].gmb = ((((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vs[0]-mos[linear].vd[0])*(1+mos[linear].lambda*(mos[linear].vs[0]-mos[linear].vd[0]))))*mos[linear].gama)/(sqrt(mos[linear].phi+mos[linear].vb[0]-mos[linear].vs[0])));       
        mos[linear].ids = -((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(mos[linear].vd[0]-mos[linear].vs[0])-(mos[linear].vd[0]-mos[linear].vs[0])*(mos[linear].vd[0]-mos[linear].vs[0]))*(1+mos[linear].lambda*(mos[linear].vd[0]-mos[linear].vs[0])));
      	//I0 = id - Gm*vgs - Gmb*vbs - Gds*vds
        mos[linear].i0 = mos[linear].ids + mos[linear].gm*(mos[linear].vg[0] + mos[linear].vs[0]) + mos[linear].gmb*(mos[linear].vb[0]-mos[linear].vs[0]) + mos[linear].rgds*(mos[linear].vd[0]-mos[linear].vs[0]);
        strcpy(mos[linear].modo,"TRIODO");
	  }
      //SATURACAO
      else if((mos[linear].vd[0]-mos[linear].vs[0])<(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])){          
        mos[linear].cgs=mos[linear].cox*mos[linear].cp*mos[linear].ld+2*(mos[linear].cox*mos[linear].cp*mos[linear].lg)/3;
        mos[linear].cgd=mos[linear].cox*mos[linear].cp*mos[linear].ld;
        mos[linear].cbg=0;    
        mos[linear].rgds = ((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(mos[linear].vs[0]-mos[linear].vg[0]+mos[linear].vt[0])*(mos[linear].vs[0]-mos[linear].vg[0]+mos[linear].vt[0])*mos[linear].lambda);
        mos[linear].gm = ((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vs[0]-mos[linear].vg[0]+mos[linear].vt[0])*(1+mos[linear].lambda*(mos[linear].vs[0]-mos[linear].vd[0]))));
        mos[linear].gmb = ((((mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(2*(mos[linear].vs[0]-mos[linear].vg[0]+mos[linear].vt[0])*(1+mos[linear].lambda*(mos[linear].vs[0]-mos[linear].vd[0]))))*mos[linear].gama)/(sqrt(mos[linear].phi-mos[linear].vs[0]+mos[linear].vb[0])));
        mos[linear].ids =  -(mos[linear].transK)*(mos[linear].cp/mos[linear].lg)*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(mos[linear].vg[0]-mos[linear].vs[0]-mos[linear].vt[0])*(1+mos[linear].lambda*(mos[linear].vd[0]-mos[linear].vs[0]));
      	//I0 = id - Gm*vgs - Gmb*vbs - Gds*vds
        mos[linear].i0 = mos[linear].ids + mos[linear].gm*(mos[linear].vg[0] + mos[linear].vs[0]) + mos[linear].gmb*(mos[linear].vb[0]-mos[linear].vs[0]) + mos[linear].rgds*(mos[linear].vd[0]-mos[linear].vs[0]);
        strcpy(mos[linear].modo,"SATURACAO");
	  }
    }
    
  } 
}

void mostraNetlist(void){
	for (i=1; i<=ne; i++) {
    tipo=netlist[i].nome[0];
    if (tipo=='R'|| tipo=='C') {
      printf("%s %d %d %g\n",netlist[i].nome,netlist[i].a,netlist[i].b,netlist[i].valor);
    }
    else if (tipo=='I' || tipo=='V'){
      printf("%s %d %d %g %g %g\n",netlist[i].nome,netlist[i].a,netlist[i].b,netlist[i].modulo,netlist[i].fase,netlist[i].valor);
    }
    else if (tipo=='G' || tipo=='E' || tipo=='F' || tipo=='H') {
      printf("%s %d %d %d %d %g\n",netlist[i].nome,netlist[i].a,netlist[i].b,netlist[i].c,netlist[i].d,netlist[i].valor);
    }
    else if (tipo=='O') {
      printf("%s %d %d %d %d\n",netlist[i].nome,netlist[i].a,netlist[i].b,netlist[i].c,netlist[i].d);
    }
    else if (tipo=='K') {
      printf("%s %s %s %g\n",netlist[i].nome,acop_K[i].lA,acop_K[i].lB,netlist[i].valor);
    }
  
  else if (tipo=='M') {
      printf("%s %s %d %d MODO: %s INVERTIDO=%d  I0 =%e Gds=%e Gm=%e Gmb=%e Cgd=%e Cbg=%e Cgs=%e\n",netlist[i].nome,netlist[i].tipo,netlist[i].a,netlist[i].b,netlist[i].modo,netlist[i].invertido,netlist[i].i0,netlist[i].rgds,netlist[i].gm,netlist[i].gmb,netlist[i].cgd,netlist[i].cbg,netlist[i].cgs);
  }
      if (tipo=='V' || tipo=='E' || tipo=='F' || tipo=='O' || tipo=='L')
      printf("Corrente jx: %d\n",netlist[i].x);
    else if (tipo=='H')
      printf("Correntes jx e jy: %d, %d\n",netlist[i].x,netlist[i].y);
  }
}

void montaEstampaDC(void){
	for (i=1; i<=ne; i++) {
        tipo=netlist[i].nome[0];
        if (tipo=='R' || tipo=='C' ) {
          g=1/netlist[i].valor;
          Yn[netlist[i].a][netlist[i].a]+=g;
          Yn[netlist[i].b][netlist[i].b]+=g;
          Yn[netlist[i].a][netlist[i].b]-=g;
          Yn[netlist[i].b][netlist[i].a]-=g;
        }
        else if (tipo=='L'){//estampa do indutor controlado a corrente (P.O.)
          g=netlist[i].valor;
          Yn[netlist[i].a][netlist[i].x]+=1;
          Yn[netlist[i].b][netlist[i].x]-=1;
          Yn[netlist[i].x][netlist[i].a]-=1;
          Yn[netlist[i].x][netlist[i].b]+=1;
          Yn[netlist[i].x][netlist[i].x]+=g;
      }
        else if (tipo=='G') {
          g=netlist[i].valor;
          Yn[netlist[i].a][netlist[i].c]+=g;
          Yn[netlist[i].b][netlist[i].d]+=g;
          Yn[netlist[i].a][netlist[i].d]-=g;
          Yn[netlist[i].b][netlist[i].c]-=g;
          
        }
        else if (tipo=='I') {
          g=netlist[i].valor;
          Yn[netlist[i].a][nv+1]-=g;
          Yn[netlist[i].b][nv+1]+=g;
        }
        else if (tipo=='V') {
          Yn[netlist[i].a][netlist[i].x]+=1;
          Yn[netlist[i].b][netlist[i].x]-=1;
          Yn[netlist[i].x][netlist[i].a]-=1;
          Yn[netlist[i].x][netlist[i].b]+=1;
          Yn[netlist[i].x][nv+1]-=netlist[i].valor;
        }
        else if (tipo=='E') {
          g=netlist[i].valor;
          Yn[netlist[i].a][netlist[i].x]+=1;
          Yn[netlist[i].b][netlist[i].x]-=1;
          Yn[netlist[i].x][netlist[i].a]-=1;
          Yn[netlist[i].x][netlist[i].b]+=1;
          Yn[netlist[i].x][netlist[i].c]+=g;
          Yn[netlist[i].x][netlist[i].d]-=g;
        }
        else if (tipo=='F') {
          g=netlist[i].valor;
          Yn[netlist[i].a][netlist[i].x]+=g;
          Yn[netlist[i].b][netlist[i].x]-=g;
          Yn[netlist[i].c][netlist[i].x]+=1;
          Yn[netlist[i].d][netlist[i].x]-=1;
          Yn[netlist[i].x][netlist[i].c]-=1;
          Yn[netlist[i].x][netlist[i].d]+=1;
        }
        else if (tipo=='H') {
          g=netlist[i].valor;
          Yn[netlist[i].a][netlist[i].y]+=1;
          Yn[netlist[i].b][netlist[i].y]-=1;
          Yn[netlist[i].c][netlist[i].x]+=1;
          Yn[netlist[i].d][netlist[i].x]-=1;
          Yn[netlist[i].y][netlist[i].a]-=1;
          Yn[netlist[i].y][netlist[i].b]+=1;
          Yn[netlist[i].x][netlist[i].c]-=1;
          Yn[netlist[i].x][netlist[i].d]+=1;
          Yn[netlist[i].y][netlist[i].x]+=g;
        }
        else if (tipo=='O') {
          Yn[netlist[i].a][netlist[i].x]+=1;
          Yn[netlist[i].b][netlist[i].x]-=1;
          Yn[netlist[i].x][netlist[i].c]+=1;
          Yn[netlist[i].x][netlist[i].d]-=1;
        }
      else if (tipo=='M') {
        linear++; 
        if(contador>1){ //entra aqui apenas a partir da segunda iteração do Newton-Raphson
          for(j=0;j<=3;j++){
                if(j==0 && tensaoMOS[linear][j]==netlist[i].a){                     
                     if (convergencia[linear][j] == 0 && contador % 10000 == 0){mos[linear].vd[0] = rand()%21 - 10;}
                     else {mos[linear].vd[0] = mos[linear].vd[1];}
                } 
              
                	else if(j==1 && tensaoMOS[linear][j]==netlist[i].c){            
                     	if (convergencia[linear][j] == 0 && contador % 10000 == 0){mos[linear].vg[0] = rand()%21 - 10;}
                      	else {mos[linear].vg[0] = mos[linear].vg[1];}
                }
              
                	else if(j==2 && tensaoMOS[linear][j]==netlist[i].b){            
                    	 if (convergencia[linear][j] == 0 && contador % 10000 == 0){mos[linear].vs[0] = rand()%21 - 10;}
                		else {mos[linear].vs[0] = mos[linear].vs[1];}
                }
          
                    else if(j==3 && tensaoMOS[linear][j]==netlist[i].d){
                     	if (convergencia[linear][j] == 0 && contador % 10000 == 0){mos[linear].vb[0] = rand()%21 - 10;}
                    	else {mos[linear].vb[0] = mos[linear].vb[1];}
                }
          }
          
            if (fabs(mos[linear].vb[0]-mos[linear].vs[0])>(mos[i].phi)/2){
              mos[linear].vt[0]=mos[i].vt0+mos[i].gama*(sqrt((mos[i].phi)/2)-sqrt(mos[i].phi));
            }
            else {
            mos[linear].vt[0]=mos[i].vt0+mos[i].gama*(sqrt(mos[i].phi-(mos[linear].vb[0]-mos[linear].vs[0]))-sqrt(mos[i].phi));
            }
            verMOSCond();            
        }
        //invertido?
        netlist[i].invertido = mos[linear].invertido;
        strcpy(netlist[i].modo,mos[linear].modo);
        //Monta o RGds
        netlist[i].rgds=mos[linear].rgds;
        g=netlist[i].rgds;          
            Yn[netlist[i].a][netlist[i].a]+=g;
            Yn[netlist[i].b][netlist[i].b]+=g;
            Yn[netlist[i].a][netlist[i].b]-=g;
            Yn[netlist[i].b][netlist[i].a]-=g; 
		//Monta I0 		
        	netlist[i].i0=mos[linear].i0;
			g=netlist[i].i0;        
          Yn[netlist[i].a][nv+1]-=g;
          Yn[netlist[i].b][nv+1]+=g;
        
		//Monta Gm
        	netlist[i].gm=mos[linear].gm;
       	 	g=netlist[i].gm;      
            Yn[netlist[i].a][netlist[i].c]+=g;
            Yn[netlist[i].b][netlist[i].b]+=g;
            Yn[netlist[i].a][netlist[i].b]-=g;
            Yn[netlist[i].b][netlist[i].c]-=g;
        //Monta Gmb        
          netlist[i].gmb=mos[linear].gmb;
          g=netlist[i].gmb;
          Yn[netlist[i].a][netlist[i].d]+=g;
          Yn[netlist[i].b][netlist[i].b]+=g;
          Yn[netlist[i].a][netlist[i].b]-=g;
          Yn[netlist[i].b][netlist[i].d]-=g;
		
		 
		//Monta CGD      
			netlist[i].cgd=mos[linear].cgd;
			g=netlist[i].cgd; 
	        Yn[netlist[i].a][netlist[i].a]+=g;
            Yn[netlist[i].c][netlist[i].c]+=g;
            Yn[netlist[i].a][netlist[i].c]-=g;
            Yn[netlist[i].c][netlist[i].a]-=g;
        
       //Monta CGS
       		netlist[i].cgs=mos[linear].cgs;
			g=netlist[i].cgs; 
	        Yn[netlist[i].c][netlist[i].c]+=g;
            Yn[netlist[i].b][netlist[i].b]+=g;
            Yn[netlist[i].c][netlist[i].b]-=g;
            Yn[netlist[i].b][netlist[i].c]-=g;
       //Monta CBG
       		netlist[i].cbg=mos[linear].cbg;
			g=netlist[i].cbg; 
	        Yn[netlist[i].c][netlist[i].c]+=g;
            Yn[netlist[i].d][netlist[i].d]+=g;
            Yn[netlist[i].c][netlist[i].d]-=g;
            Yn[netlist[i].d][netlist[i].c]-=g;  
			}
		}
	}

void montaEstampaAC(void){
		for (i=0; i<=nv; i++) {
      for (j=0; j<=nv+1; j++)
        YnComplex[i][j]=0.0 + 0.0*I;
    }
  linear = 0;
  for (i=1; i<=ne; i++) {
        tipo = netlist[i].nome[0];
        if (tipo=='R') {
          g=1/netlist[i].valor;
          YnComplex[netlist[i].a][netlist[i].a]+=g;
          YnComplex[netlist[i].b][netlist[i].b]+=g;
          YnComplex[netlist[i].a][netlist[i].b]-=g;
          YnComplex[netlist[i].b][netlist[i].a]-=g;
        }
        else if (tipo=='C' ) {//estampa do capacitor (resp em freq)
          inc_C++;      
          gComplex=2*PI*frequencia*cap_C[inc_C]*I;
          YnComplex[netlist[i].a][netlist[i].a]+=gComplex;
          YnComplex[netlist[i].b][netlist[i].b]+=gComplex;
          YnComplex[netlist[i].a][netlist[i].b]-=gComplex;
          YnComplex[netlist[i].b][netlist[i].a]-=gComplex;
        }
        else if (tipo=='L'){//estampa do indutor controlado a corrente (resp em freq)
          inc_L++;
          gComplex=2*PI*frequencia*ind_L[inc_L]*I;printf("\nInd: %g",ind_L[inc_L]);
          YnComplex[netlist[i].a][netlist[i].x]+=1;
          YnComplex[netlist[i].b][netlist[i].x]-=1;
          YnComplex[netlist[i].x][netlist[i].a]-=1;
          YnComplex[netlist[i].x][netlist[i].b]+=1;
          YnComplex[netlist[i].x][netlist[i].x]+=gComplex;
        }
        else if (tipo=='G') {
          g=netlist[i].valor;
          YnComplex[netlist[i].a][netlist[i].c]+=g;
          YnComplex[netlist[i].b][netlist[i].d]+=g;
          YnComplex[netlist[i].a][netlist[i].d]-=g;
          YnComplex[netlist[i].b][netlist[i].c]-=g;
          
        }
        else if (tipo=='I') {
            YnComplex[netlist[i].a][nv+1]-= netlist[i].modulo*cosd(netlist[i].fase) + netlist[i].modulo*sind(netlist[i].fase)*I;
            YnComplex[netlist[i].b][nv+1]+= netlist[i].modulo*cosd(netlist[i].fase) + netlist[i].modulo*sind(netlist[i].fase)*I;
		}
        else if (tipo=='V') {
            YnComplex[netlist[i].a][netlist[i].x]+=1;
            YnComplex[netlist[i].b][netlist[i].x]-=1;
            YnComplex[netlist[i].x][netlist[i].a]-=1;
            YnComplex[netlist[i].x][netlist[i].b]+=1;
            
            YnComplex[netlist[i].x][nv+1]-=netlist[i].modulo*cosd(netlist[i].fase) + netlist[i].modulo*sind(netlist[i].fase)*I;
			
        
		}
        else if (tipo=='E') {
          g=netlist[i].valor;
          YnComplex[netlist[i].a][netlist[i].x]+=1;
          YnComplex[netlist[i].b][netlist[i].x]-=1;
          YnComplex[netlist[i].x][netlist[i].a]-=1;
          YnComplex[netlist[i].x][netlist[i].b]+=1;
          YnComplex[netlist[i].x][netlist[i].c]+=g;
          YnComplex[netlist[i].x][netlist[i].d]-=g;
        }
        else if (tipo=='F') {
          g=netlist[i].valor;
          YnComplex[netlist[i].a][netlist[i].x]+=g;
          YnComplex[netlist[i].b][netlist[i].x]-=g;
          YnComplex[netlist[i].c][netlist[i].x]+=1;
          YnComplex[netlist[i].d][netlist[i].x]-=1;
          YnComplex[netlist[i].x][netlist[i].c]-=1;
          YnComplex[netlist[i].x][netlist[i].d]+=1;
        }
        else if (tipo=='H') {
          g=netlist[i].valor;
          YnComplex[netlist[i].a][netlist[i].y]+=1;
          YnComplex[netlist[i].b][netlist[i].y]-=1;
          YnComplex[netlist[i].c][netlist[i].x]+=1;
          YnComplex[netlist[i].d][netlist[i].x]-=1;
          YnComplex[netlist[i].y][netlist[i].a]-=1;
          YnComplex[netlist[i].y][netlist[i].b]+=1;
          YnComplex[netlist[i].x][netlist[i].c]-=1;
          YnComplex[netlist[i].x][netlist[i].d]+=1;
          YnComplex[netlist[i].y][netlist[i].x]+=g;
        }
        else if (tipo=='O') {
          YnComplex[netlist[i].a][netlist[i].x]+=1;
          YnComplex[netlist[i].b][netlist[i].x]-=1;
          YnComplex[netlist[i].x][netlist[i].c]+=1;
          YnComplex[netlist[i].x][netlist[i].d]-=1;
        }
      else if (tipo=='M'){   
        linear++; 
          
        	//MONTA RGDS
        	netlist[i].rgds = mos[linear].rgds;
	    	gComplex=netlist[i].rgds; 
            YnComplex[netlist[i].a][netlist[i].a]+=gComplex;
            YnComplex[netlist[i].b][netlist[i].b]+=gComplex;
            YnComplex[netlist[i].a][netlist[i].b]-=gComplex;
            YnComplex[netlist[i].b][netlist[i].a]-=gComplex;  
        	
			//MONTA I0			
        	netlist[i].i0 = mos[linear].i0;
	    	gComplex=netlist[i].i0; 
            YnComplex[netlist[i].a][nv+1]=gComplex;
            YnComplex[netlist[i].b][nv+1]=gComplex;
				//MONTA GM
        	  netlist[i].gm = mos[linear].gm;
	    	  gComplex=netlist[i].gm;         
            YnComplex[netlist[i].a][netlist[i].c]+=gComplex;
            YnComplex[netlist[i].b][netlist[i].b]+=gComplex;
            YnComplex[netlist[i].a][netlist[i].b]-=gComplex;
            YnComplex[netlist[i].b][netlist[i].c]-=gComplex;
        
        	  //MONTA GMB
        	  netlist[i].gmb = mos[linear].gmb;
	    	  gComplex=netlist[i].gmb; 
          YnComplex[netlist[i].a][netlist[i].d]+=gComplex;
          YnComplex[netlist[i].b][netlist[i].b]+=gComplex;
          YnComplex[netlist[i].a][netlist[i].b]-=gComplex;
          YnComplex[netlist[i].b][netlist[i].d]-=gComplex;
			//MONTA CGD
		  gComplex=2*PI*frequencia*mos[linear].cgd*I;
	        YnComplex[netlist[i].a][netlist[i].a]+=gComplex;
            YnComplex[netlist[i].c][netlist[i].c]+=gComplex;
            YnComplex[netlist[i].a][netlist[i].c]-=gComplex;
            YnComplex[netlist[i].c][netlist[i].a]-=gComplex;
        
        //MONTA CGS  
		  gComplex=2*PI*frequencia*mos[linear].cgs*I;
	        YnComplex[netlist[i].c][netlist[i].c]+=gComplex;
            YnComplex[netlist[i].b][netlist[i].b]+=gComplex;
            YnComplex[netlist[i].c][netlist[i].b]-=gComplex;
            YnComplex[netlist[i].b][netlist[i].c]-=gComplex;
        
        //MONTA CBG
          gComplex=2*PI*frequencia*mos[linear].cbg*I;
	        YnComplex[netlist[i].c][netlist[i].c]+=gComplex;
            YnComplex[netlist[i].d][netlist[i].d]+=gComplex;
            YnComplex[netlist[i].c][netlist[i].d]-=gComplex;
            YnComplex[netlist[i].d][netlist[i].c]-=gComplex;
        }
            
      else if (tipo=='K'){
        fim = 0;
        for (indice = 1; indice <= ne && fim != 2; indice++){
            if(strcmp(acop_K[i].lA, netlist[indice].nome) == 0){
                fim++;
                valorLA = netlist[i].valor;
            }
            else if(strcmp(acop_K[i].lB, netlist[indice].nome) == 0){
                fim++;
                valorLB = netlist[i].valor;
            }
        }

        ind_M = netlist[i].valor*(sqrt(valorLA*valorLB));      
        YnComplex[netlist[i].a][netlist[i].x]+=1;
        YnComplex[netlist[i].b][netlist[i].x]-=1;
        YnComplex[netlist[i].c][netlist[i].y]+=1;
        YnComplex[netlist[i].d][netlist[i].y]-=1;
        YnComplex[netlist[i].x][netlist[i].a]-=1;
        YnComplex[netlist[i].x][netlist[i].b]+=1;
        YnComplex[netlist[i].y][netlist[i].c]-=1;
        YnComplex[netlist[i].y][netlist[i].d]+=1;
        YnComplex[netlist[i].x][netlist[i].x]+=2*PI*frequencia*valorLA*I;
        YnComplex[netlist[i].x][netlist[i].y]+=2*PI*frequencia*ind_M*I;
        YnComplex[netlist[i].y][netlist[i].x]+=2*PI*frequencia*ind_M*I;
        YnComplex[netlist[i].y][netlist[i].y]+=2*PI*frequencia*valorLB*I;
  
    }
    
  }
}

void verificaConvergencia(void)
{
	for(k=1;k<=linear;k++) {        
      /*se nv estiver associada a alguma das 4 tensóes de cada um dos MOSFETS*/
      /*i: roda o numero de variáveis do sistema, j: roda as 4 tensões de cada MOS, k: roda o numero de MOS(qtde de elementos nao lineares no circuito)*/
       for (i=1; i<=ne; i++){
        if (netlist[i].nome[0]=='M'){        
            for(j=0;j<=3;j++){
  
          	if(j==0){
              mos[k].vd[1]=Yn[i][nv+1];
              if ((mos[k].vd[1] > 1) && (fabs((mos[k].vd[1]-mos[k].vd[0])/mos[k].vd[1]) < 1e-12))
                  {convergencia[k][j] = 1;}
              else if ((mos[k].vd[1] <= 1) && (fabs(mos[k].vd[1]-mos[k].vd[0])<1e-12))
                  {convergencia[k][j] = 1;}                  
              else {
                  (convergencia[k][j] = 0);
                  mos[k].vd[0]=mos[k].vd[1];
              }
          }
            
          else  if(j==1){
              mos[k].vg[1]=Yn[i][nv+1];
              if ((mos[k].vg[1] > 1) && (fabs((mos[k].vg[1]-mos[k].vg[0])/mos[k].vg[1]) < 1e-12))
                  {convergencia[k][j] = 1;}
              else if ((mos[k].vg[1] <= 1) && (fabs(mos[k].vg[1]-mos[k].vg[0])<1e-12))
                  {convergencia[k][j] = 1;}                  
              else {
                  (convergencia[k][j] = 0);
                  mos[k].vg[0]=mos[k].vg[1];
              }
          }
            
        else  if(j==2){
              mos[k].vs[1]=Yn[i][nv+1];
              if ((mos[k].vs[1] > 1) && (fabs((mos[k].vs[1]-mos[k].vs[0])/mos[k].vs[1]) < 1e-12))
                  {convergencia[k][j] = 1;}
              else if ((mos[k].vs[1] <= 1) && (fabs(mos[k].vs[1]-mos[k].vs[0])<1e-12))
                  {convergencia[k][j] = 1;}                  
              else {
                  (convergencia[k][j] = 0);
                  mos[k].vs[0]=mos[k].vs[1];
              }
          }
        else  if(j==3){
              mos[k].vb[1]=Yn[i][nv+1];
              if ((mos[k].vb[1] > 1) && (fabs((mos[k].vb[1]-mos[k].vb[0])/mos[k].vb[1]) < 1e-12))
                  {convergencia[k][j] = 1;}
              else if ((mos[k].vb[1] <= 1) && (fabs(mos[k].vb[1]-mos[k].vb[0])<1e-12))
                  {convergencia[k][j] = 1;}                  
              else {
                  (convergencia[k][j] = 0);
                  mos[k].vb[0]=mos[k].vb[1];
              }
          }
        
      }

      } 
      
    }
	}
}
/* Resolucao de sistema de equacoes lineares.
   Metodo de Gauss-Jordan com condensacao pivotal */
int resolversistema(void)
{
  int i,j,l,a;
  double t, p;

  for (i=1; i<=nv; i++) {
    t=0.0;
    a=i;
    for (l=i; l<=nv; l++) {
      if (fabs(Yn[l][i])>fabs(t)) {
      a=l;
      t=Yn[l][i];
      }
    }
    if (i!=a) {
      for (l=1; l<=nv+1; l++) {
  p=Yn[i][l];
  Yn[i][l]=Yn[a][l];
  Yn[a][l]=p;
      }
    }
    if (fabs(t)<TOLG) {
      printf("Sistema singular\n");
      return 1;
    }
    for (j=nv+1; j>0; j--) {  /* Basta j>i em vez de j>0 */
      Yn[i][j]/= t;
      p=Yn[i][j];
      if (p!=0)  /* Evita operacoes com zero */
        for (l=1; l<=nv; l++) {  
    if (l!=i)
      Yn[l][j]-=Yn[l][i]*p;
        }
    }
  }
  return 0;
}

int resolversistemaAC(void)
{
  int i,j,l,a;
  double complex t, p;

  for (i=1; i<=nv; i++) {
    t=0.0 + 0.0 * I;
    a=i;
    for (l=i; l<=nv; l++) {
      if (cabs(YnComplex[l][i])>cabs(t)) {
  		a=l;
  		t=YnComplex[l][i];
      }
    }
    if (i!=a) {
      for (l=1; l<=nv+1; l++) {
  p=YnComplex[i][l];
  YnComplex[i][l]=YnComplex[a][l];
  YnComplex[a][l]=p;
      }
    }
    if (cabs(t)<TOLG) {
      printf("Sistema singular\n");
      return 1;
    }
    for (j=nv+1; j>0; j--) {  /* Basta j>i em vez de j>0 */
      YnComplex[i][j]/= t;
      p=YnComplex[i][j];
      if (cabs(p)!=0.0)  /* Evita operacoes com zero */
        for (l=1; l<=nv; l++) {  
    if (l!=i)
      YnComplex[l][j]-=YnComplex[l][i]*p;
        }
    }
  }
  return 0;
}

/* Rotina que conta os nos e atribui numeros a eles */
int numero(char *nome)
{
  int i,achou;

  i=0; achou=0;
  while (!achou && i<=nv)
    if (!(achou=!strcmp(nome,lista[i]))) i++;
  if (!achou) {
    if (nv==MAX_NOS) {
      printf("O programa so aceita ate %d nos\n",nv);
      exit(1);
    }
    nv++;
    strcpy(lista[nv],nome);
    return nv; /* novo no */
  }
  else {
    return i; /* no ja conhecido */
  }
}
/*void clrscr() {
  #ifdef WINDOWS
  system("cls");
  #endif
  #ifdef LINUX
  system("clear");
  #endif
}*/

int main(void)
{
  //clrscr();
  printf("Programa de analise de Ponto de Operacao e Resposta em Frenquencia com MOSFET\n");
  printf("Por: Fernanda Cassinelli\nLucas do Vale\nLucas Miranda\n");
  printf("Versao %s\n",versao);
 denovo:
  /* Leitura do netlist */
  ne=0; nv=0; inc_L=0; inc_C=0; 
  ne_extra=0; linear=0; strcpy(lista[0],"0");
  printf("Nome do arquivo com o netlist (ex: mna.net): ");
  scanf("%50s",nomearquivo);
  arquivo=fopen(nomearquivo,"r");
  if (arquivo==0) {
    printf("Arquivo %s inexistente\n",nomearquivo);
    goto denovo;
  }
  printf("\nAnalise no Ponto de Operacao (P.O.)\n\n");
  printf("Lendo netlist:\n");
  fgets(txt,MAX_LINHA,arquivo);
  printf("Titulo: %s",txt);
  
  char largura[11], comprimento[11], subLarg[10], subComp[10];
  
  
  while (fgets(txt,MAX_LINHA,arquivo)) { //leitura do netlist linha por linha
    ne++; /* Nao usa o netlist[0] */
    if (ne>MAX_ELEM) {
      printf("O programa so aceita ate %d elementos\n",MAX_ELEM);
      exit(1);
    }
    txt[0]=toupper(txt[0]);
    tipo=txt[0];
    sscanf(txt,"%10s",netlist[ne].nome);
    p=txt+strlen(netlist[ne].nome);/* Inicio dos parametros */
    /* O que e lido depende do tipo */
    if (tipo=='R' || tipo=='L' || tipo=='C') {
      sscanf(p,"%10s%10s%lg",na,nb,&netlist[ne].valor);
    if (tipo=='L') {     //substitui a indutancia pela baixa resistencia e armazena a indutancia em outra var
      inc_L++;  
      ind_L[inc_L] = netlist[ne].valor;
      netlist[ne].valor = 1e-9;
      printf("%s %s %s %g\n",netlist[ne].nome,na,nb,ind_L[inc_L]);
    }
    else if (tipo=='C') {     //substitui a capacitancia pela alta resistencia e armazena a capacitancia em outra var
      inc_C++;
          cap_C[inc_C] = netlist[ne].valor;
      netlist[ne].valor = 1e9;
      printf("%s %s %s %g\n",netlist[ne].nome,na,nb,cap_C[inc_C]);
    }
    else{ 
      printf("%s %s %s %g\n",netlist[ne].nome,na,nb,netlist[ne].valor);
    }
      netlist[ne].a=numero(na);
      netlist[ne].b=numero(nb);
  }
  else if (tipo=='I' || tipo=='V'){
    sscanf(p,"%10s%10s%lg%lg%lg",na,nb,&netlist[ne].modulo,&netlist[ne].fase,&netlist[ne].valor);
    printf("%s %s %s %g %g %g\n",netlist[ne].nome,na,nb,netlist[ne].modulo,netlist[ne].fase,netlist[ne].valor);
    netlist[ne].a=numero(na);
    netlist[ne].b=numero(nb);
    }
  
  else if (tipo=='K') {
    sscanf(p,"%10s%10s%lg",acop_K[ne].lA,acop_K[ne].lB,&netlist[ne].valor);
    printf("%s %s %s %g\n",netlist[ne].nome,acop_K[ne].lA,acop_K[ne].lB,netlist[ne].valor);
  }
  
    else if (tipo=='G' || tipo=='E' || tipo=='F' || tipo=='H') {
      sscanf(p,"%10s%10s%10s%10s%lg",na,nb,nc,nd,&netlist[ne].valor);
      printf("%s %s %s %s %s %g\n",netlist[ne].nome,na,nb,nc,nd,netlist[ne].valor);
      netlist[ne].a=numero(na);
      netlist[ne].b=numero(nb);
      netlist[ne].c=numero(nc);
      netlist[ne].d=numero(nd);
    }
    else if (tipo=='O') {
      sscanf(p,"%10s%10s%10s%10s",na,nb,nc,nd);
      printf("%s %s %s %s %s\n",netlist[ne].nome,na,nb,nc,nd);
      netlist[ne].a=numero(na);
      netlist[ne].b=numero(nb);
      netlist[ne].c=numero(nc);
      netlist[ne].d=numero(nd);
    }
    
    else if (tipo=='M') {
      srand(time(NULL));
      linear++;
      sscanf(p,"%10s%10s%10s%10s%10s%10s%10s%lg%lg%lg%lg%lg%lg",na,nb,nc,nd,mos[linear].tipo,comprimento,largura,&mos[linear].transK,&mos[linear].vt0,&mos[linear].lambda,&mos[linear].gama,&mos[linear].phi,&mos[linear].ld);
      
      if (mos[linear].tipo[0]=='N')
      	mos[linear].cox=(2*mos[linear].transK)/0.05;
      else if (mos[linear].tipo[0]=='P')
      	mos[linear].cox=(2*mos[linear].transK)/0.02;
      
    //retira os termos "L=" e "W="
    strncpy(subLarg, largura + 2, 9);
      strncpy(subComp, comprimento + 2, 9);
      subLarg[9] = '\0';
      subComp[9] = '\0';
      sscanf(subLarg, "%lg", &mos[linear].lg);
      sscanf(subComp, "%lg", &mos[linear].cp);
      
    printf("%s %s %s %s %s %s %g %g %g %g %g %g %g %g\n",netlist[ne].nome,na,nb,nc,nd,mos[linear].tipo,mos[linear].cp,mos[linear].lg,mos[linear].transK,mos[linear].vt0,mos[linear].lambda,mos[linear].gama,mos[linear].phi,mos[linear].ld);
      //TransistorMOS: M<nome> <nód> <nóg> <nós> <nób> <NMOS ou PMOS> L=<comprimento> W=<largura> <K> <Vt0> <lambda> <gama> <phi> <Ld>
    	
 	  strcpy(netlist[ne].tipo,mos[linear].tipo);   
	  mos[linear].vd[0]=0.1;
	  mos[linear].vg[0]=0.1;
	  mos[linear].vs[0]=0.1;
      mos[linear].vb[0]=mos[linear].phi/2+mos[linear].vs[0]; //valores iniciais aleatórios entre 0 e 1 para as tensões
      mos[linear].vt[0]=mos[linear].vt0+mos[linear].gama*(sqrt(mos[linear].phi-(mos[linear].vb[0]-mos[linear].vs[0]))-sqrt(mos[linear].phi));     
      verMOSCond();
	  //resistor RDS
      netlist[ne].a=numero(na); tensaoMOS[linear][0]=netlist[ne].a; // 0 -> vd associado ao numero do no pela 1 vez
      netlist[ne].b=numero(nc); tensaoMOS[linear][2]=netlist[ne].b; // 2 -> vs associado ao numero do no pela 1 vez
      netlist[ne].rgds=mos[linear].rgds;      
      //transcondutancia Gm
      netlist[ne].c=numero(nb); tensaoMOS[linear][1]=netlist[ne].c; // 1 -> vg associado ao numero do no pela 1 vez
      netlist[ne].gm=mos[linear].gm;
      //transcondutancia Gmb
      netlist[ne].d=numero(nd); tensaoMOS[linear][3]=netlist[ne].d; // 3 -> vb associado ao numero do no pela 1 vez
      netlist[ne].gmb=mos[linear].gmb;
      //fonte de corrente I0
      netlist[ne].i0= mos[linear].i0;      
      //capacitancia CGD      
      netlist[ne].cgd=1e9;
      //capacitancia CGS     
      netlist[ne].cgs=1e9;
      //capacitancia CGB
      netlist[ne].cbg=1e9;    
    }
    else if (tipo=='.'){
    	sscanf(p,"%10s %lg %lg %lg",escala,&pontos,&freqInicial,&freqFinal);
    	printf("%s %s %g %g %g",netlist[ne].nome,escala,pontos,freqInicial,freqFinal);
    	tem=1;
	}
    
    else if (tipo=='*') { /* Comentario comeca com "*" */
      printf("Comentario: %s",txt);
      ne--;
    }
    else {
      printf("Elemento desconhecido: %s\n",txt);
      getch();
      exit(1);
    }
  }
 
  
  fclose(arquivo);
  /* Acrescenta variaveis de corrente acima dos nos, anotando no netlist */
  nn=nv;
  for (i=1; i<=ne; i++) {
    tipo=netlist[i].nome[0];
    if (tipo=='V' || tipo=='E' || tipo=='F' || tipo=='O' || tipo=='L') {
      nv++;
      if (nv>MAX_NOS) {
        printf("As correntes extra excederam o numero de variaveis permitido (%d)\n",MAX_NOS);
        exit(1);
      }
      strcpy(lista[nv],"j"); /* Tem espaco para mais dois caracteres */
      strcat(lista[nv],netlist[i].nome);
      netlist[i].x=nv;
    }
    else if (tipo=='H') {
      nv=nv+2;
      if (nv>MAX_NOS) {
        printf("As correntes extra excederam o numero de variaveis permitido (%d)\n",MAX_NOS);
        exit(1);
      }
      strcpy(lista[nv-1],"jx"); strcat(lista[nv-1],netlist[i].nome);
      netlist[i].x=nv-1;
      strcpy(lista[nv],"jy"); strcat(lista[nv],netlist[i].nome);
      netlist[i].y=nv;
    }
  }
  getch();
  /* Lista tudo */
  printf("\nVariaveis internas: \n");
  for (i=0; i<=nv; i++)
	printf("%d -> %s\n",i,lista[i]);
  getch();
   /* Monta o sistema nodal modificado */
  if(linear>0) {
    printf("O circuito e nao linear. Seu modelo linearizado tem %d nos, %d variaveis, %d elementos lineares e %d elementos nao lineares (que se decompoe em %d elementos linearizados)., com ne=%d\n",nn,nv,ne-linear,linear,linear*7,ne);
  }
  else {
    printf("O circuito e linear.  Tem %d nos, %d variaveis e %d elementos\n",nn,nv,ne);
  }
  getch();
  /* Zera sistema */
  for (i=0; i<=nv; i++) {
    for (j=0; j<=nv+1; j++)
      Yn[i][j]=0;
  }
  //Zera matriz de convergencia
  for (i=0; i<=MAX_ELEM; i++) {
    for (j=0; j<4; j++)
      convergencia[i][j]=0;
  }
  
  /* Monta estampas */
  while(fim==0){
     linear=0;                       
     montaEstampaDC();        
      /* Resolve o sistema */
    if (resolversistema()) {
      //mostraNetlist();
      getch();
      exit;
    }
    verificaConvergencia(); 
    contador++;
    for (i = 1; (i <=linear)&&(i != -1);){
    	for(j=0;j<4;j++){
		if (convergencia[i][j] == 1) {i++;}
      else {i = -1;}
  		}
    }  
    if (i==linear){fim = 1;}
    if (contador==10000){fim =1;}    
  }//fim do while
  
  
  printf("Netlist interno final:\n");
  mostraNetlist();
  getch();
  
  printf("\n%d iteracoes foram realizadas.\n",contador);
  contador=0;
  
  printf("\n%d Elementos nao lineares\n",linear);
  for(i=1;i<=linear;i++){
    for(j = 0; j <4; j++){
    if (convergencia[i][j] == 0){contador++;}
  		}
	}
	for(i=1;i<=linear;i++){	
  		for(j=1;j<4;j++){
    printf("\n Convergencia %d %d",j,convergencia[i][j]);
 		 }
  	}
  if(contador!=0)
    printf("\n%d solucoes nao convergiram. Ultima solucao do sistema:\n",contador);
  else
    printf("Solucao do Ponto de Operacao:\n");

  strcpy(txt,"Tensao");
  for (i=1; i<=nv; i++) {
    if (i==nn+1) strcpy(txt,"Corrente");
    printf("%s %s: %g\n",txt,lista[i],Yn[i][nv+1]);
  }
  
  
  //RESPOSTA EM FREQUENCIA 
  
  
  if(tem==1){
	printf("\nAnalise de Resposta em Frequencia:\n");	
	
	for (i=0; i<=nv; i++) {
      for (j=0; j<=nv+1; j++)
        YnComplex[i][j]=0.0 + 0.0*I;
    }
   
    trocaNome();
  
  if(strcmp(escala,"LIN")==0){
  	
	passo=(freqFinal-freqInicial)/(pontos-1);
  	
	arquivo = fopen(novonome, "w");
	fprintf(arquivo,"f ");
	for (i=1; i<=nv; i++)
		fprintf(arquivo,"%sm %sf ",lista[i],lista[i]);
	fprintf(arquivo,"\n");
	
	if(arquivo == NULL)
		printf("Erro, nao foi possivel abrir o arquivo\n");
	else{
		
  		for(frequencia=freqInicial;frequencia<=freqFinal;frequencia+=passo){
  		  		inc_L=0; inc_C=0;
  		  		linear=0;
				montaEstampaAC();
  		  		resolversistemaAC();

			fprintf(arquivo,"%g ",frequencia);
			for (i=1; i<=nv; i++) {
    			fprintf(arquivo,"%g %g ",cabs(YnComplex[i][nv+1]),carg(YnComplex[i][nv+1]));
  			}	
			fprintf(arquivo,"\n");  				
	  	}
	  	
	}
	fclose(arquivo);
	getch();
  }
  else if (strcmp(escala,"DEC")==0){
  	passo=1/(pontos-1);
  	
  	arquivo = fopen(novonome, "w");
  	fprintf(arquivo,"f ");
	for (i=1; i<=nv; i++)
		fprintf(arquivo,"%sm %sf ",lista[i],lista[i]);
	fprintf(arquivo,"\n");
  	
	if(arquivo == NULL)
		printf("Erro, nao foi possivel abrir o arquivo\n");
    else{
		
  		for(frequencia=freqInicial;frequencia<=freqFinal;frequencia*=pow(10,passo)){
  		  	inc_L=0; inc_C=0;
  		  	linear=0;
			montaEstampaAC();
  		  	resolversistemaAC();
			
			fprintf(arquivo,"%g ",frequencia);
			for (i=1; i<=nv; i++) {
				//	printf("\n%g + %gj: ",creal(YnComplex[i][nv+1]),cimag(YnComplex[i][nv+1]));
    			fprintf(arquivo,"%g %g ",cabs(YnComplex[i][nv+1]),carg(YnComplex[i][nv+1]));
  			}	
			fprintf(arquivo,"\n");  			
	  	}
	  	
    }
	fclose(arquivo);
	getch();
  }
  	  
   else if (strcmp(escala,"OCT")==0){
  		passo=1/(pontos-1);
  		
  		arquivo = fopen(novonome, "w");
  		fprintf(arquivo,"f ");
	    for (i=1; i<=nv; i++)
		  	fprintf(arquivo,"%sm %sf ",lista[i],lista[i]);
	    fprintf(arquivo,"\n");
  		
		if(arquivo == NULL)
			printf("Erro, nao foi possivel abrir o arquivo\n");
    	else{
			
  			for(frequencia=freqInicial;frequencia<=freqFinal;frequencia*=pow(2,passo)){
  		  		inc_L=0; inc_C=0;
  		  		linear=0;
				montaEstampaAC();
  		  		resolversistemaAC();

				fprintf(arquivo,"%g ",frequencia);
				for (i=1; i<=nv; i++) {
    				fprintf(arquivo,"%g %g ",cabs(YnComplex[i][nv+1]),carg(YnComplex[i][nv+1]));
  				}	
				fprintf(arquivo,"\n");  				
	  		}
	  	}
		fclose(arquivo);
		getch();
  	}
	
}
else if (tem==0){
	printf("Sistema possui apenas Ponto de Operacao");
	getch();
	exit(1);
}
       /*if (resolversistemaAC()) {
      getch();
      exit;
  }
  getch();
  
  strcpy(txt,"Tensao");
  for (i=1; i<=nv; i++) {
    if (i==nn+1) strcpy(txt,"Corrente");
    printf("%s %s: %g + %gi \n",txt,lista[i],creal(YnComplex[i][nv+1]),cimag(YnComplex[i][nv+1]));
  }*/
  
  return 0;

}
