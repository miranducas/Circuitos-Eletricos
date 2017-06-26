/*
Circuitos Eletricos 2
Prof. Antonio Carlos Moreirao Queiroz
Grupo: Fernanda F. B. Cassinelli,  Ian Secchin e Rodrigo Ferreira.
Programa de analise de circuitos lineares contendo transistores bipolares,  encontrando o ponto de
operação e a resposta em frequência para pequenos sinais.
*/

/*
Descricao do circuito:
Resistor:      R<nome> <no1> <no2> <resistencia>
Indutor:       L<nome> <no1> <no2> <indutancia>
Acoplamento:   K<nome> <La> <Lb> <k> (La e Lb já declarados)
Capacitor:     C<nome> <no2> <no2> <capacitancia>
VCVC:          E<nome> <noV+> <noV-> <nov+> <nov-> <Av>
CCCS:          F<nome> <noI+> <noI-> <noi+> <noi-> <Ai>
VCCS:          G<nome> <noI+> <noI-> <nov+> <nov-> <Gm>
CCVS:          H<nome> <noV+> <noV-> <noi+> <noi-> <Rm>
Fonte I:       I<nome> <no+> <no-> <modulo> <fase> <valor continuo> (fase em graus)
Fonte V:       V<nome> <no+> <no-> <modulo> <fase> <valor continuo> (fase em graus)
Amp. Op.:      O<nome> <no saida+> <no saida-> <no entrada+> <no entrada->
BJT:           Q<nome> <noc> <nob> <noe> <tipo> <alfa> <alfar> <Isbe> <VTbe> <Isbc> <VTbc> <VA> <C0be> <C1be> <C0bc> <C1bc>
Comentario:    *<comentario>
*/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>
#include <math.h>
#include <complex.h>
#include <time.h>

#define MAX_CHAR_LINHA      80
#define MAX_NOME            11
#define MAX_NOME_ARQUIVO    20
#define MAX_ELEMENTOS       500
#define MAX_NOS             50
#define TOLG                1e-30
#define PI                  3.14159265358979
#define UM                  0.999999999999999999999999999999999999999999
#define ZERO                0.0000000000000000000000000000000000000001
#define VMAX_DIODO          0.7
#define FI_DIODO            0.6

typedef struct infoIndutor {
    double indutancia;
} infoIndutor;

typedef struct infoCapacitor {
    double capacitancia;
} infoCapacitor;


typedef struct acoplar {
    char lA[MAX_NOME], lB[MAX_NOME];
} acoplar;

typedef struct infoBJT {
    int noc, nob, noe;
    char tipo[MAX_NOME];
    double alfa, alfar, isbc, vtbc, isbe, vtbe, va, cZerobe, cUmbe, cZerobc,cUmbc;
} infoBJT;

typedef struct infoElementos {
    char nome[MAX_NOME], tipo[MAX_NOME], modo[MAX_NOME];
    double valor, modulo, fase;
    int a, b, c, d, x, y;
    double gm,  rm, cZerobe, cUmbe, cZerobc,cUmbc;
    int invertido;
} infoElementos;

acoplar acoplamento[MAX_ELEMENTOS];
infoElementos netlist[MAX_ELEMENTOS];
infoIndutor indutor[MAX_ELEMENTOS];
infoCapacitor capacitor[MAX_ELEMENTOS];
infoBJT bjt[MAX_ELEMENTOS];

int
    numeroVariaveis, fim, numeroNos, tem, nC, nL, nBJTs, nElementos,
    listaNos[MAX_NOS], contador, convergencia[MAX_NOS], L1,L2;

char
    escala[3],
    noA[MAX_NOME], noB[MAX_NOME], noC[MAX_NOME], noD[MAX_NOME],
    *p,
    *novonome,
    *txt,
    elemento,
    linha[MAX_CHAR_LINHA],
    file[MAX_NOME_ARQUIVO];

double
    pontos, freqInicial, freqFinal, frequencia, Yn[MAX_NOS + 1][MAX_NOS + 2], g,
    variavelAtual[MAX_NOS], variavelProxima[MAX_NOS],
    VC, VB, VE, VBC, VBE, VCE, gc, ge, g1, g2, g3, vMaxExp, vbcAux, vbeAux,
    ic, ie, i0, cbcdir, cbcrev, cbedir, cberev, indutanciaMutua, passo;

double complex
    gComplex, amplitude, fase,
    YnComplex[MAX_NOS + 1][MAX_NOS+2];  //matriz nodal com complexos (análise da resposta em frequencia)

FILE *arquivo;

int no(char *nome)
{
    int i;
    int numeroNo = atoi(nome);

    if (numeroVariaveis == 0) {
        listaNos[0] = numeroNo;
        numeroVariaveis++;

        return numeroNo;
    }

    for (i = 0; i < numeroVariaveis; i++) {
        if (numeroNo == listaNos[i]) {
            return numeroNo;
        }
    }

    if (i == MAX_NOS - 1) {
        printf("O numero maximo de %u nos foi ultrapassado.\n", MAX_NOS);
        exit(1);
    }

    listaNos[numeroVariaveis] = numeroNo;
    numeroVariaveis++;

    return numeroNo;
}

double sind(double ang)
{
    double t = sin((ang / 180.0) * PI);
    if (fabs(t) > UM) {
        return (1.0);
    }
    if (fabs(t) < ZERO) {
        return (0.0);
    }

    return (t);
}


double cosd (double ang)
{
    double t = cos((ang / 180.0) * PI);

    if (fabs(t) > UM) {
        return (1.0);
    }
    /*
    if ( t < -UM) {
        return (-1.0);
    }
    */
    if (fabs(t) < ZERO) {
        return (0.0);
    }

    return (t);
}

//rotina que troca extensao de .net para .tab
void trocaNome()
{
    int n = 0;
    do {
        n++;
    } while (file[n] != '.');

    memcpy(novonome, &file[0], n);
    novonome[n] = '\0';
    strcpy(novonome, strcat(novonome, ".tab"));
    printf("Resultados escritos no arquivo %s\n", novonome);
}

int resolverSistemaDC(void)
{
    int i, j, l, a;
    double t, p;

    for (i = 1; i <=numeroVariaveis; i++) {
        t = 0.0;
        a = i;
        for (l = i; l < numeroVariaveis; l++) {
            if (fabs(Yn[l][i]) > fabs(t)) {
                a = l;
                t = Yn[l][i];
            }
        }
        if (i != a) {
            for (l = 0; l < numeroVariaveis + 1; l++) {
                p = Yn[i][l];
                Yn[i][l] = Yn[a][l];
                Yn[a][l] = p;
            }
        }
        if (fabs(t) < TOLG) {
            printf("Sistema DC singular\n");
            return 1;
        }
        for (j = numeroVariaveis + 1; j > 0; j--) {  /* Basta j>i em vez de j>0 */
            Yn[i][j] /= t;
            p = Yn[i][j];
            if (p != 0) { /* Evita operacoes com zero */
                for (l = 0; l < numeroVariaveis; l++) {
                    if (l != i) {
                        Yn[l][j] -= Yn[l][i] * p;
                    }
                }
            }
        }
    }

    return 0;
}

int resolversistemaAC(void)
{
    int i, j, l, a;
    double complex t, p;

    for (i = 1; i <= numeroVariaveis; i++) {
        t = 0.0 + 0.0 * I;
        a = i;
        for (l = i; l <= numeroVariaveis; l++) {
            if (cabs(YnComplex[l][i]) > cabs(t)) {
                a = l;
                t = YnComplex[l][i];
            }
        }
        if (i != a) {
            for (l = 1; l <= numeroVariaveis + 1; l++) {
                p = YnComplex[i][l];
                YnComplex[i][l] = YnComplex[a][l];
                YnComplex[a][l] = p;
            }
        }
        if (cabs(t) < TOLG) {
            printf("Sistema AC singular\n");
            return 1;
        }
        for (j = numeroVariaveis + 1; j > 0; j--) {  /* Basta j>i em vez de j>0 */
            YnComplex[i][j] /= t;
            p = YnComplex[i][j];
            if (cabs(p) != 0.0) { /* Evita operacoes com zero */
                for (l = 1; l <= numeroVariaveis; l++) {
                    if (l != i) {
                        YnComplex[l][j] -= YnComplex[l][i] * p;
                    }
                }
            }
        }
    }

    return 0;
}

void verificaConvergencia(void)
{
    int i;

    for (i = 1;i <= numeroVariaveis; i++) {
        variavelProxima[i] = 0;
        variavelProxima[i] = Yn[i][numeroVariaveis + 1];
        if (contador % 1000 != 0) {
            if (fabs(variavelProxima[i]) > 1 && fabs((variavelProxima[i] - variavelAtual[i]) / variavelProxima[i]) < 1e-9) {
                convergencia[i] = 1;
                variavelAtual[i] = variavelProxima[i];
            }
            else if (fabs(variavelProxima[i]) <= 1 && fabs(variavelProxima[i] - variavelAtual[i]) < 1e-9) {
                convergencia[i] = 1;
                variavelAtual[i] = variavelProxima[i];
            }
            else {
                convergencia[i] = 0;
                variavelAtual[i] = variavelProxima[i];
            }
        }
        else if (contador % 1000 == 0) {
            if (i > numeroNos) {
                variavelAtual[i] = (rand() % 11) - 5;
            }
            else {
                variavelAtual[i] = (rand() % 21) - 10;
            }
        }
    }
}

void mostraEstampaDC(void)
{
    int indiceI, indiceJ;

    for (indiceI = 1; indiceI <= numeroVariaveis; indiceI++) {
        printf("\n");
        for (indiceJ = 1; indiceJ <= numeroVariaveis + 1; indiceJ++) {
            printf("%+3.1f ", Yn[indiceI][indiceJ]);
        }
    }

    printf("\n\n");
}

void montaEstampaDC(void)
{
    int i, j;
    char tipo;

    for (i = 1; i <= nElementos; i++) {
        tipo = netlist[i].nome[0];
        printf("%s\n", netlist[i].nome);

        if (tipo == 'R' || tipo == 'C' ) {
            g = 1.0/netlist[i].valor;
            Yn[netlist[i].a][netlist[i].a] += g;
            Yn[netlist[i].b][netlist[i].b] += g;
            Yn[netlist[i].a][netlist[i].b] -= g;
            Yn[netlist[i].b][netlist[i].a] -= g;
            mostraEstampaDC();
        }
        else if (tipo == 'L') {  //estampa do indutor controlado a corrente (P.O.)
            g = netlist[i].valor;

            Yn[netlist[i].a][netlist[i].x] += 1;
            Yn[netlist[i].b][netlist[i].x] -= 1;
            Yn[netlist[i].x][netlist[i].a] -= 1;
            Yn[netlist[i].x][netlist[i].b] += 1;
            Yn[netlist[i].x][netlist[i].x] += g;
        }
        else if (tipo == 'G') {
            g = netlist[i].valor;

            Yn[netlist[i].a][netlist[i].c] += g;
            Yn[netlist[i].b][netlist[i].d] += g;
            Yn[netlist[i].a][netlist[i].d] -= g;
            Yn[netlist[i].b][netlist[i].c] -= g;

        }
        else if (tipo == 'I') {
            g = netlist[i].valor;
            Yn[netlist[i].a][numeroVariaveis + 1] -= g;
            Yn[netlist[i].b][numeroVariaveis + 1] += g;
        }
        else if (tipo == 'V') {
            Yn[netlist[i].a][netlist[i].x] += 1;
            Yn[netlist[i].b][netlist[i].x] -= 1;
            Yn[netlist[i].x][netlist[i].a] -= 1;
            Yn[netlist[i].x][netlist[i].b] += 1;
            Yn[netlist[i].x][numeroVariaveis + 1] -= netlist[i].valor;
        }
        else if (tipo == 'E') {
            g = netlist[i].valor;

            Yn[netlist[i].a][netlist[i].x] += 1;
            Yn[netlist[i].b][netlist[i].x] -= 1;
            Yn[netlist[i].x][netlist[i].a] -= 1;
            Yn[netlist[i].x][netlist[i].b] += 1;
            Yn[netlist[i].x][netlist[i].c] += g;
            Yn[netlist[i].x][netlist[i].d] -= g;
        }
        else if (tipo == 'F') {
            g = netlist[i].valor;

            Yn[netlist[i].a][netlist[i].x] += g;
            Yn[netlist[i].b][netlist[i].x] -= g;
            Yn[netlist[i].c][netlist[i].x] += 1;
            Yn[netlist[i].d][netlist[i].x] -= 1;
            Yn[netlist[i].x][netlist[i].c] -= 1;
            Yn[netlist[i].x][netlist[i].d] += 1;
        }
        else if (tipo == 'H') {
            g = netlist[i].valor;

            Yn[netlist[i].a][netlist[i].y] += 1;
            Yn[netlist[i].b][netlist[i].y] -= 1;
            Yn[netlist[i].c][netlist[i].x] += 1;
            Yn[netlist[i].d][netlist[i].x] -= 1;
            Yn[netlist[i].y][netlist[i].a] -= 1;
            Yn[netlist[i].y][netlist[i].b] += 1;
            Yn[netlist[i].x][netlist[i].c] -= 1;
            Yn[netlist[i].x][netlist[i].d] += 1;
            Yn[netlist[i].y][netlist[i].x] += g;
        }
        else if (tipo == 'Q') {
            VC  = variavelAtual[netlist[i].a];
            VB  = variavelAtual[netlist[i].b];
            VE  = variavelAtual[netlist[i].c];
            VBC = variavelAtual[netlist[i].b] - variavelAtual[netlist[i].a];
            VBE = variavelAtual[netlist[i].b] - variavelAtual[netlist[i].c];
            VCE = variavelAtual[netlist[i].a] - variavelAtual[netlist[i].c];

            if ((int) bjt[i].tipo == 'N') {
                vMaxExp = VMAX_DIODO;
                vbcAux  = (VBC > vMaxExp) ? vMaxExp : VBC;
                vbeAux  = (VBE > vMaxExp) ? vMaxExp : VBE;

                cbcrev = (vbcAux>0.3) ? bjt[i].cZerobc / pow(0.5, 0.5) : bjt[i].cZerobc / pow((1.0 - (vbcAux / FI_DIODO)), 0.5);
                cbcdir = (vbcAux>0)   ? bjt[i].cUmbc * (exp(vbcAux / bjt[i].vtbc) - 1) : 0;

                cberev = (vbeAux>0.3) ? bjt[i].cZerobe / pow(0.5, 0.5) : bjt[i].cZerobe / pow((1.0 - (vbeAux / FI_DIODO)), 0.5);
                cbedir = (vbeAux>0)   ? bjt[i].cUmbe * (exp(vbeAux / bjt[i].vtbe) - 1) : 0;
            }
            else {
                if (contador == 0) {
                    bjt[i].isbe = -bjt[i].isbe;
                    bjt[i].vtbe = -bjt[i].vtbe;
                    bjt[i].isbc = -bjt[i].isbc;
                    bjt[i].vtbc = -bjt[i].vtbc;
                    bjt[i].va   = -bjt[i].va;
                }

                vMaxExp = -VMAX_DIODO;
                vbcAux  = (VBC < vMaxExp) ? vMaxExp : VBC;
                vbeAux  = (VBE < vMaxExp) ? vMaxExp : VBE;

                cbcrev = (-vbcAux > 0.3) ? bjt[i].cZerobc / pow(0.5, 0.5) : bjt[i].cZerobc / pow((1.0 - ((-vbcAux) / FI_DIODO)), 0.5);
                cbcdir = (-vbcAux > 0)   ? bjt[i].cUmbc * (exp(vbcAux / bjt[i].vtbc) - 1) : 0;

                cberev = (-vbeAux > 0.3) ? bjt[i].cZerobe / pow(0.5, 0.5) : bjt[i].cZerobe / pow((1.0 - ((-vbeAux) / FI_DIODO)), 0.5);
                cbedir = (-vbeAux > 0)   ? bjt[i].cUmbe * (exp(vbeAux / bjt[i].vtbe) - 1) : 0;
            }

            /*DIODO BC  */
            gc = (bjt[i].isbc / bjt[i].vtbc) * exp(vbcAux / bjt[i].vtbc);
            ic = bjt[i].isbc * (exp(vbcAux / bjt[i].vtbc) - 1) - gc * vbcAux;
            /*DIODO BE  */
            ge = (bjt[i].isbe / bjt[i].vtbe) * exp(vbeAux / bjt[i].vtbe);
            ie = bjt[i].isbe * (exp(vbeAux / bjt[i].vtbe) - 1) - ge * vbeAux;
            /*EARLY  */
            g1 = bjt[i].alfa * ge * VCE / bjt[i].va;
            g2 = -gc * VCE / bjt[i].va;
            g3 = (bjt[i].alfa * (ie + ge * VBE) - (ic + gc * VBC)) / bjt[i].va;
            i0 = -(g1 * VBE) - (g2 * VBC);

            g = gc;
            Yn[netlist[i].a][netlist[i].a] += g;
            Yn[netlist[i].b][netlist[i].b] += g;
            Yn[netlist[i].a][netlist[i].b] -= g;
            Yn[netlist[i].b][netlist[i].a] -= g;

            g = ic;
            Yn[netlist[i].a][numeroVariaveis + 1] += g;
            Yn[netlist[i].b][numeroVariaveis + 1] -= g;

            g = bjt[i].alfa * ge;
            Yn[netlist[i].a][netlist[i].b] += g;
            Yn[netlist[i].b][netlist[i].c] += g;
            Yn[netlist[i].a][netlist[i].c] -= g;
            Yn[netlist[i].b][netlist[i].b] -= g;

            g = bjt[i].alfa * ie;
            Yn[netlist[i].a][numeroVariaveis + 1] -= g;
            Yn[netlist[i].b][numeroVariaveis + 1] += g;

            g = ge;
            Yn[netlist[i].b][netlist[i].b] += g;
            Yn[netlist[i].c][netlist[i].c] += g;
            Yn[netlist[i].b][netlist[i].c] -= g;
            Yn[netlist[i].c][netlist[i].b] -= g;

            g = ie;
            Yn[netlist[i].b][numeroVariaveis + 1] -= g; //???
            Yn[netlist[i].c][numeroVariaveis + 1] += g; //???

            g = bjt[i].alfar * gc;
            Yn[netlist[i].c][netlist[i].b] += g;
            Yn[netlist[i].b][netlist[i].a] += g;
            Yn[netlist[i].c][netlist[i].a] -= g;
            Yn[netlist[i].b][netlist[i].b] -= g;

            g = bjt[i].alfar * ic;
            Yn[netlist[i].c][numeroVariaveis + 1] -= g;
            Yn[netlist[i].b][numeroVariaveis + 1] += g;

            /*efeito early */
            g = i0;
            Yn[netlist[i].a][numeroVariaveis + 1] -= g;
            Yn[netlist[i].c][numeroVariaveis + 1] += g;

            g = g1;
            Yn[netlist[i].a][netlist[i].b] += g;
            Yn[netlist[i].c][netlist[i].c] += g;
            Yn[netlist[i].a][netlist[i].c] -= g;
            Yn[netlist[i].c][netlist[i].b] -= g;

            g = g2;
            Yn[netlist[i].a][netlist[i].b] += g;
            Yn[netlist[i].c][netlist[i].a] += g;
            Yn[netlist[i].a][netlist[i].a] -= g;
            Yn[netlist[i].c][netlist[i].b] -= g;

            g = g3;
            Yn[netlist[i].a][netlist[i].a] += g;
            Yn[netlist[i].c][netlist[i].c] += g;
            Yn[netlist[i].a][netlist[i].c] -= g;
            Yn[netlist[i].c][netlist[i].a] -= g;

            // capacitores em DC
            Yn[netlist[i].b][netlist[i].b] += 1e9;
            Yn[netlist[i].a][netlist[i].a] += 1e9;
            Yn[netlist[i].b][netlist[i].a] -= 1e9;
            Yn[netlist[i].a][netlist[i].b] -= 1e9;

            Yn[netlist[i].b][netlist[i].b] += 1e9;
            Yn[netlist[i].c][netlist[i].c] += 1e9;
            Yn[netlist[i].b][netlist[i].c] -= 1e9;
            Yn[netlist[i].c][netlist[i].b] -= 1e9;
        } // end of if 'Q'
        mostraEstampaDC();
    } // end of for
} // end of montaEstampaDC

void montaEstampaAC(void)
{
    int i, j;
    char tipo;

    for (i = 0; i <= numeroVariaveis + 1; i++) {
        for (j = 0; j <= numeroVariaveis + 1; j++) {
            YnComplex[i][j] = 0.0 + 0.0 * I;
        }
    }

    for (i = 1; i <= nElementos; i++) {
        tipo = netlist[i].nome[0];

        if (tipo == 'R') {
            g = 1 / netlist[i].valor;
            YnComplex[netlist[i].a][netlist[i].a] += g;
            YnComplex[netlist[i].b][netlist[i].b] += g;
            YnComplex[netlist[i].a][netlist[i].b] -= g;
            YnComplex[netlist[i].b][netlist[i].a] -= g;
        }
        else if (tipo == 'C' ) {//estampa do capacitor (resp em freq)
            netlist[i].valor = capacitor[i].capacitancia;
            gComplex = 2 * PI * frequencia * capacitor[i].capacitancia * I;

            YnComplex[netlist[i].a][netlist[i].a] += gComplex;
            YnComplex[netlist[i].b][netlist[i].b] += gComplex;
            YnComplex[netlist[i].a][netlist[i].b] -= gComplex;
            YnComplex[netlist[i].b][netlist[i].a] -= gComplex;
        }
        else if (tipo == 'L') {//estampa do indutor controlado a corrente (resp em freq)
            netlist[i].valor = indutor[i].indutancia;
            gComplex = 2 * PI * frequencia * indutor[i].indutancia * I;

            YnComplex[netlist[i].a][netlist[i].x] += 1;
            YnComplex[netlist[i].b][netlist[i].x] -= 1;
            YnComplex[netlist[i].x][netlist[i].a] -= 1;
            YnComplex[netlist[i].x][netlist[i].b] += 1;
            YnComplex[netlist[i].x][netlist[i].x] += gComplex;
        }
        else if (tipo == 'G') {
            g = netlist[i].valor;

            YnComplex[netlist[i].a][netlist[i].c] += g;
            YnComplex[netlist[i].b][netlist[i].d] += g;
            YnComplex[netlist[i].a][netlist[i].d] -= g;
            YnComplex[netlist[i].b][netlist[i].c] -= g;
        }
        else if (tipo == 'I') {
            YnComplex[netlist[i].a][numeroVariaveis + 1] -= netlist[i].modulo * cosd(netlist[i].fase) + netlist[i].modulo * sind(netlist[i].fase) * I;
            YnComplex[netlist[i].b][numeroVariaveis + 1] += netlist[i].modulo * cosd(netlist[i].fase) + netlist[i].modulo * sind(netlist[i].fase) * I;
        }
        else if (tipo == 'V') {
            YnComplex[netlist[i].a][netlist[i].x] += 1;
            YnComplex[netlist[i].b][netlist[i].x] -= 1;
            YnComplex[netlist[i].x][netlist[i].a] -= 1;
            YnComplex[netlist[i].x][netlist[i].b] += 1;
            YnComplex[netlist[i].x][numeroVariaveis + 1] -= (netlist[i].modulo * cosd(netlist[i].fase) + netlist[i].modulo * sind(netlist[i].fase) * I);
        }
        else if (tipo == 'E') {
            g = netlist[i].valor;

            YnComplex[netlist[i].a][netlist[i].x] += 1;
            YnComplex[netlist[i].b][netlist[i].x] -= 1;
            YnComplex[netlist[i].x][netlist[i].a] -= 1;
            YnComplex[netlist[i].x][netlist[i].b] += 1;
            YnComplex[netlist[i].x][netlist[i].c] += g;
            YnComplex[netlist[i].x][netlist[i].d] -= g;
        }
        else if (tipo == 'F') {
            g = netlist[i].valor;

            YnComplex[netlist[i].a][netlist[i].x] += g;
            YnComplex[netlist[i].b][netlist[i].x] -= g;
            YnComplex[netlist[i].c][netlist[i].x] += 1;
            YnComplex[netlist[i].d][netlist[i].x] -= 1;
            YnComplex[netlist[i].x][netlist[i].c] -= 1;
            YnComplex[netlist[i].x][netlist[i].d] += 1;
        }
        else if (tipo == 'H') {
            g = netlist[i].valor;

            YnComplex[netlist[i].a][netlist[i].y] += 1;
            YnComplex[netlist[i].b][netlist[i].y] -= 1;
            YnComplex[netlist[i].c][netlist[i].x] += 1;
            YnComplex[netlist[i].d][netlist[i].x] -= 1;
            YnComplex[netlist[i].y][netlist[i].a] -= 1;
            YnComplex[netlist[i].y][netlist[i].b] += 1;
            YnComplex[netlist[i].x][netlist[i].c] -= 1;
            YnComplex[netlist[i].x][netlist[i].d] += 1;
            YnComplex[netlist[i].y][netlist[i].x] += g;
        }
        else if (tipo == 'O') {
            YnComplex[netlist[i].a][netlist[i].x] += 1;
            YnComplex[netlist[i].b][netlist[i].x] -= 1;
            YnComplex[netlist[i].x][netlist[i].c] += 1;
            YnComplex[netlist[i].x][netlist[i].d] -= 1;
        }
        else if (tipo == 'K') {
            fim = 0;

            int indice;
            for (indice = 0; indice < nElementos && fim != 2; indice++) {
                if (strcmp(acoplamento[i].lA, netlist[indice].nome) == 0) {
                    fim++;
                    L1 = indice;
                }
                else if (strcmp(acoplamento[i].lB, netlist[indice].nome) == 0) {
                    fim++;
                    L2 = indice;
                }
            }

            indutanciaMutua = netlist[i].valor * (sqrt(indutor[L1].indutancia * indutor[L2].indutancia));
            YnComplex[netlist[L1].x][netlist[L2].x] += 2 * PI * frequencia * indutanciaMutua * I;
            YnComplex[netlist[L2].x][netlist[L1].x] += 2 * PI * frequencia * indutanciaMutua * I;
        }
        else if (tipo == 'Q') {
            if ((int) bjt[i].tipo == 'N') {
                vMaxExp = VMAX_DIODO;
                vbcAux  = (VBC > vMaxExp) ? vMaxExp : VBC;
                vbeAux  = (VBE > vMaxExp) ? vMaxExp : VBE;
                cbcrev  = (vbcAux > 0.3) ? netlist[i].cZerobc/pow(0.5, 0.5) : netlist[i].cZerobc / pow((1.0 - (vbcAux / FI_DIODO)), 0.5);
                cbcdir  = (vbcAux > 0)   ? bjt[i].cUmbc * (exp(vbcAux / bjt[i].vtbc) - 1) : 0;

                cberev = (vbeAux>0.3) ? bjt[i].cZerobe / pow(0.5, 0.5) : bjt[i].cZerobe / pow((1.0 - (vbeAux / FI_DIODO)), 0.5);
                cbedir = (vbeAux>0)   ? bjt[i].cUmbe * (exp(vbeAux / bjt[i].vtbe) - 1) : 0;
            }
            else { /* PNP */
                vMaxExp = -VMAX_DIODO;
                vbcAux  = ((VBC)<vMaxExp)? vMaxExp:(VBC);
                vbeAux  = ((VBE)<vMaxExp)? vMaxExp:(VBE);

                cbcrev = (-vbcAux > 0.3) ? netlist[i].cZerobc / pow(0.5, 0.5) : netlist[i].cZerobc / pow((1.0 - ((-vbcAux) / FI_DIODO)), 0.5);
                cbcdir = (-vbcAux > 0)   ? bjt[i].cUmbc * (exp(vbcAux / bjt[i].vtbc) - 1) : 0;

                cberev = (-vbeAux > 0.3) ? bjt[i].cZerobe / pow(0.5, 0.5) : bjt[i].cZerobe / pow((1.0 - ((-vbeAux) / FI_DIODO)), 0.5);
                cbedir = (-vbeAux > 0)   ? bjt[i].cUmbe * (exp(vbeAux / bjt[i].vtbe) - 1) : 0;
            }

             /*DIODO BC  */
            gc = (bjt[i].isbc / bjt[i].vtbc) * exp(vbcAux / bjt[i].vtbc);
            ic = bjt[i].isbc * (exp(vbcAux / bjt[i].vtbc) - 1) - gc * vbcAux;
             /*DIODO BE  */
            ge = (bjt[i].isbe / bjt[i].vtbe) * exp(vbeAux / bjt[i].vtbe);
            ie = bjt[i].isbe * (exp(vbeAux / bjt[i].vtbe) - 1) - ge * vbeAux;
             /*EARLY  */
            g1 = bjt[i].alfa * ge * VCE / bjt[i].va;
            g2 = -gc * VCE / bjt[i].va;
            g3 = (bjt[i].alfa * (ie + ge * VBE) - (ic + gc * VBC)) / bjt[i].va;
            i0 = -(g1 * VBE) - (g2 * VBC);

            g = gc;
            YnComplex[netlist[i].a][netlist[i].a] += g;
            YnComplex[netlist[i].b][netlist[i].b] += g;
            YnComplex[netlist[i].a][netlist[i].b] -= g;
            YnComplex[netlist[i].b][netlist[i].a] -= g;

            g = bjt[i].alfa * ge;
            YnComplex[netlist[i].a][netlist[i].b] += g;
            YnComplex[netlist[i].b][netlist[i].c] += g;
            YnComplex[netlist[i].a][netlist[i].c] -= g;
            YnComplex[netlist[i].b][netlist[i].b] -= g;

            g = ge;
            YnComplex[netlist[i].b][netlist[i].b] += g;
            YnComplex[netlist[i].c][netlist[i].c] += g;
            YnComplex[netlist[i].b][netlist[i].c] -= g;
            YnComplex[netlist[i].c][netlist[i].b] -= g;

            g = bjt[i].alfar * gc;
            YnComplex[netlist[i].a][netlist[i].b] += g;
            YnComplex[netlist[i].b][netlist[i].c] += g;
            YnComplex[netlist[i].a][netlist[i].c] -= g;
            YnComplex[netlist[i].b][netlist[i].b] -= g;

            /*efeito early */
            g = g1;
            YnComplex[netlist[i].a][netlist[i].b] += g;
            YnComplex[netlist[i].c][netlist[i].c] += g;
            YnComplex[netlist[i].a][netlist[i].c] -= g;
            YnComplex[netlist[i].c][netlist[i].b] -= g;

            g = g2;
            YnComplex[netlist[i].a][netlist[i].b] += g;
            YnComplex[netlist[i].c][netlist[i].a] += g;
            YnComplex[netlist[i].a][netlist[i].a] -= g;
            YnComplex[netlist[i].c][netlist[i].b] -= g;

            g = g3;
            YnComplex[netlist[i].a][netlist[i].a] += g;
            YnComplex[netlist[i].c][netlist[i].c] += g;
            YnComplex[netlist[i].a][netlist[i].c] -= g;
            YnComplex[netlist[i].c][netlist[i].a] -= g;

            /*Creversa diodo bc */
            gComplex = I * PI * 2 * freqInicial * cbcrev;
            YnComplex[netlist[i].b][netlist[i].b] += gComplex;
            YnComplex[netlist[i].a][netlist[i].a] += gComplex;
            YnComplex[netlist[i].b][netlist[i].a] -= gComplex;
            YnComplex[netlist[i].a][netlist[i].b] -= gComplex;

            /*Cdireta diodo bc */
            gComplex = I * PI * 2 * freqInicial * cbcdir;
            YnComplex[netlist[i].b][netlist[i].b] += gComplex;
            YnComplex[netlist[i].a][netlist[i].a] += gComplex;
            YnComplex[netlist[i].b][netlist[i].a] -= gComplex;
            YnComplex[netlist[i].a][netlist[i].b] -= gComplex;

            /*Creversa diodo be */
            gComplex = I * PI * 2 * freqInicial * cberev;
            YnComplex[netlist[i].b][netlist[i].b] += gComplex;
            YnComplex[netlist[i].c][netlist[i].c] += gComplex;
            YnComplex[netlist[i].b][netlist[i].c] -= gComplex;
            YnComplex[netlist[i].c][netlist[i].b] -= gComplex;

            /*Cdireta diodo be */
            gComplex = I * PI * 2 * freqInicial * cbedir;
            YnComplex[netlist[i].b][netlist[i].b] += gComplex;
            YnComplex[netlist[i].c][netlist[i].c] += gComplex;
            YnComplex[netlist[i].b][netlist[i].c] -= gComplex;
            YnComplex[netlist[i].c][netlist[i].b] -= gComplex;
        } // end if tipo = 'Q'
    }
}

int main(void)
{
    printf("Programa de Analise de Ponto de Operacao e Resposta em Frenquencia de Circuitos com BJT\n");
    printf("Por: Fernanda Cassinelli,  Ian Secchin,  Rodrigo Ferreira\n");
    nElementos = 0; nL = 0; nC = 0; nBJTs = 0; numeroVariaveis = 0;

    printf("Arquivo com o netlist: ");
    scanf("%50s", file);

    arquivo = fopen(file, "r");
    if (arquivo == 0) {
        printf("O arquivo %s nao existe.\n", file);
        exit(1);
    }
    printf("Lendo o netlist...\n\n");

    fgets(linha, MAX_CHAR_LINHA, arquivo);
    printf("Titulo: %s\n", linha);

    while (fgets(linha, MAX_CHAR_LINHA, arquivo)) {
        nElementos++;
        if (nElementos > MAX_ELEMENTOS) {
            printf("O netlist nao pode ter mais que %d elementos.\n", MAX_ELEMENTOS);
            exit(1);
        }

        linha[0] = toupper(linha[0]);
        elemento = linha[0];
        sscanf(linha, "%10s",  netlist[nElementos].nome); // nome do elemento
        p = linha + strlen(netlist[nElementos].nome);

        if (elemento == 'R' || elemento == 'L' || elemento == 'C') { // R, C, L <nome> <no1> <no2> <valor>
            sscanf(p, "%10s%10s%lg", noA, noB, &netlist[nElementos].valor);
            if (elemento == 'L') {
                indutor[nElementos].indutancia = netlist[nElementos].valor;
                netlist[nElementos].valor = 1e-9; // valor para a analise DC (curto)
                printf("%s %s %s %g\n", netlist[nElementos].nome, noA, noB, indutor[nElementos].indutancia);
                nL++;
            }
            else if (elemento == 'C') {
                capacitor[nElementos].capacitancia = netlist[nElementos].valor;
                netlist[nElementos].valor = 1e9; // valor para a analise DC (aberto)
                printf("%s %s %s %g\n", netlist[nElementos].nome, noA, noB, capacitor[nElementos].capacitancia);
                nC++;
            }
            else {
                printf("%s %s %s %g\n", netlist[nElementos].nome, noA, noB, netlist[nElementos].valor);
            }

            netlist[nElementos].a = no(noA); // retorna o numero referente a um no ja existente ou um novo no
            netlist[nElementos].b = no(noB);
        }
        else if (elemento == 'I' || elemento == 'V') { // I<nome> <no+> <no-> <modulo> <fase> <valor continuo> (fase em graus)
            sscanf(p, "%10s%10s%lg%lg%lg", noA, noB, &netlist[nElementos].modulo, &netlist[nElementos].fase, &netlist[nElementos].valor);
            printf("%s %s %s %g %g %g\n", netlist[nElementos].nome, noA, noB, netlist[nElementos].modulo, netlist[nElementos].fase, netlist[nElementos].valor);
            netlist[nElementos].a = no(noA);
            netlist[nElementos].b = no(noB);
        }
        else if (elemento == 'K') { // K<nome> <La> <Lb> <k> (La e Lb já declarados)
            sscanf(p, "%10s%10s%lg", acoplamento[nElementos].lA, acoplamento[nElementos].lB, &netlist[nElementos].valor);
            printf("%s %s %s %g\n", netlist[nElementos].nome, acoplamento[nElementos].lA, acoplamento[nElementos].lB, netlist[nElementos].valor);
        }
        else if (elemento == 'G' || elemento == 'E' || elemento == 'F' || elemento == 'H') {
            sscanf(p, "%10s%10s%10s%10s%lg", noA, noB, noC, noD, &netlist[nElementos].valor);
            printf("%s %s %s %s %s %g\n", netlist[nElementos].nome, noA, noB, noC, noD, netlist[nElementos].valor);
            netlist[nElementos].a = no(noA);
            netlist[nElementos].b = no(noB);
            netlist[nElementos].c = no(noC);
            netlist[nElementos].d = no(noD);
        }
        else if (elemento == 'O') {
            sscanf(p, "%10s%10s%10s%10s", noA, noB, noC, noD);
            printf("%s %s %s %s %s\n", netlist[nElementos].nome, noA, noB, noC, noD);
            netlist[nElementos].a = no(noA);
            netlist[nElementos].b = no(noB);
            netlist[nElementos].c = no(noC);
            netlist[nElementos].d = no(noD);
        }
        else if (elemento == 'Q') { // Q<nome> <noc> <nob> <noe> <tipo> <alfa> <alfar> <Isbe> <VTbe> <Isbc> <VTbc> <VA> <C0be> <C1be> <C0bc> <C1bc>
            //srand(time(NULL));
            nBJTs++;
            sscanf(p, "%10s%10s%10s%10s%lg%lg%lg%lg%lg%lg%lg%lg%lg%lg%lg", noA, noB, noC, bjt[nElementos].tipo, &bjt[nElementos].alfa, &bjt[nElementos].alfar, &bjt[nElementos].isbe, &bjt[nElementos].vtbe, &bjt[nElementos].isbc, &bjt[nElementos].vtbc, &bjt[nElementos].va, &bjt[nElementos].cZerobe, &bjt[nElementos].cUmbe, &bjt[nElementos].cZerobc, &bjt[nElementos].cUmbc);
            printf("%s %s %s %s %s %lg %lg %lg %lg %lg %lg %lg %lg %lg %lg %lg\n", netlist[nElementos].nome, noA, noB, noC, bjt[nElementos].tipo, bjt[nElementos].alfa, bjt[nElementos].alfar, bjt[nElementos].isbe, bjt[nElementos].vtbe, bjt[nElementos].isbc, bjt[nElementos].vtbc, bjt[nElementos].va, bjt[nElementos].cZerobe, bjt[nElementos].cUmbe, bjt[nElementos].cZerobc, bjt[nElementos].cUmbc);
            strcpy(netlist[nElementos].tipo, bjt[nElementos].tipo);
            netlist[nElementos].a = no(noA);
            netlist[nElementos].b = no(noB);
            netlist[nElementos].c = no(noC);

            bjt[nElementos].noc = netlist[nElementos].a;
            bjt[nElementos].nob = netlist[nElementos].b;
            bjt[nElementos].noe = netlist[nElementos].c;

            netlist[nElementos].cZerobe = 1e9; // valor para a analise dc
            netlist[nElementos].cUmbe = 1e9;
            netlist[nElementos].cZerobc = 1e9;
            netlist[nElementos].cUmbc = 1e9;
        }
        else if (elemento == '.') {
            sscanf(p, "%10s %lg %lg %lg", escala, &pontos, &freqInicial, &freqFinal);
            printf("%s %s %g %g %g\n", netlist[nElementos].nome, escala, pontos, freqInicial, freqFinal);
            tem = 1;
        }
        else if (elemento == '*') { /* Comentario comeca com "*" */
            printf("Comentario: %s\n", linha);
            nElementos--;
        }
        else {
            printf("Elemento desconhecido: %s\n", linha);
            exit(1);
        }
    }

    fclose(arquivo);

    int i;
    printf("\nNos: ");
    for (i = 0; i < numeroVariaveis; i++) {
        printf("%u", listaNos[i]);
    }
    printf("\n\n");

    numeroNos = numeroVariaveis;
    char stringNumero[MAX_NOME], lista[MAX_NOS+1][MAX_NOME+2]; // PRECISA DO +1???????????????????????????????????????????
    for (i = 0; i < numeroVariaveis; i++) {
        sprintf(stringNumero, "%u", listaNos[i]);
        strcpy(lista[i], stringNumero);
    }

    char tipo;

    for (i = 0; i < nElementos; i++) {
        tipo = netlist[i].nome[0];
        if (tipo == 'V' || tipo == 'E' || tipo == 'F' || tipo == 'O' || tipo == 'L') {
            numeroVariaveis++;
            if (numeroVariaveis > MAX_NOS) {
                printf("As correntes extra excederam o numero de variaveis permitido (%d)\n", MAX_NOS);
                exit(1);
            }
            strcpy(lista[numeroVariaveis - 1],"j"); /* Tem espaco para mais dois caracteres */
            sprintf(stringNumero, "%u", numeroVariaveis - 1);
            strcat(lista[numeroVariaveis - 1], stringNumero);
            netlist[i].x = numeroVariaveis;
        }
        else if (tipo == 'H') {
            numeroVariaveis = numeroVariaveis + 2;
            if (numeroVariaveis > MAX_NOS) {
                printf("As correntes extra excederam o numero de variaveis permitido (%d)\n", MAX_NOS);
                exit(1);
            }
            strcpy(lista[numeroVariaveis - 2],"jx");
            sprintf(stringNumero, "%u", numeroVariaveis - 2);
            strcat(lista[numeroVariaveis - 2], stringNumero);
            netlist[i].x = numeroVariaveis - 2;
            strcpy(lista[numeroVariaveis - 1],"jy");
            sprintf(stringNumero, "%u", numeroVariaveis - 1);
            strcat(lista[numeroVariaveis - 1],stringNumero);
            netlist[i].y = numeroVariaveis - 1;
        }
    }

    /* Lista tudo */
    printf("Variaveis internas: \n");
    for (i = 0; i < numeroVariaveis; i++)
    printf("%d -> %s\n", i, lista[i]);
    printf("\n");

    /* Monta o sistema nodal modificado */
    if (nBJTs > 0) {
        printf("O circuito e nao linear. Seu modelo linearizado tem %d nos, %d variaveis, %d elementos lineares e %d elementos nao lineares (que se decompoe em %d elementos linearizados)., com nElementos=%d\n", numeroNos, numeroVariaveis, nElementos - nBJTs, nBJTs, nBJTs * 7, nBJTs);
    }
    else {
        printf("O circuito e linear. Tem %d nos, %d variaveis e %d elementos\n", numeroNos, numeroVariaveis, nElementos);
    }

    int j;
    for (i = 0; i < numeroVariaveis; i++) {
        for (j = 0; j < numeroVariaveis + 1; j++) {
            Yn[i][j] = 0;
        }
    }

    mostraEstampaDC();

    /* Monta estampas */
    int k = 0;
    while (fim == 0) {
        contador++;
        nBJTs = 0;
        /* Zera sistema */
        montaEstampaDC();
        /* Resolve o sistema */
        if (resolverSistemaDC()) {
            exit(1);
        }
        /*
        if (contador == 1) {
            mostraNetlist();
        }
        */

        verificaConvergencia();

        for (k = 0; (k < numeroVariaveis) && (k != -1);) {
            if (convergencia[k] == 1) {
                k++;
            }
            else {
                k = -1;
            }
        }
        if ((k == numeroVariaveis + 1) || (contador == 10000) || (nBJTs == 0)) {
            fim = 1;
        }
    }//fim do while


    //printf("Netlist interno final:\n");
    //mostraNetlist();

    printf("%d iteracoes foram realizadas.\n", contador);
    contador = 0;
    printf("%d Elementos nao lineares\n", nBJTs);
    for (i = 0; i < nBJTs; i++) {
        for (j = 0; j < numeroVariaveis; j++) {
            if (convergencia[j] == 0) {
                contador++;
            }
        }
    }

    if (nBJTs != 0) {
        for (i = 0; i < numeroVariaveis; i++) {
            printf("Convergencia na variavel %d : %d\n", i, convergencia[i]);
        }
    }

    printf("Numero de nos: %d\n", k);
    if (contador != 0) {
        printf("%d solucoes nao convergiram. Ultima solucao do sistema:\n", contador);
    }
    else {
        printf("Solucao do Ponto de Operacao:\n");
    }

    strcpy(txt,"Tensao");
    for (i = 0; i< numeroVariaveis; i++) {
        if (i == numeroNos + 1) {
            strcpy(txt,"Corrente");
        }
       printf("%s %s: %g\n", txt, lista[i], Yn[i][numeroVariaveis + 1]);
    }


    //RESPOSTA EM FREQUENCIA

    if (tem == 1) {
        printf("Analise de Resposta em Frequencia:\n");

        for (i = 0; i <= numeroVariaveis; i++) {
            for (j = 0; j<= numeroVariaveis + 1; j++) {
                YnComplex[i][j]=0.0 + 0.0 * I;
            }
        }
        trocaNome();

        if (strcmp(escala, "LIN") == 0) {
            passo = (freqFinal - freqInicial) / (pontos + 1);

            arquivo = fopen(novonome, "w");
            fprintf(arquivo, "f ");
            for (i = 0; i< numeroVariaveis; i++) {
                fprintf(arquivo, "%sm %sf ", lista[i], lista[i]);
            }
            fprintf(arquivo, "\n");

            if (arquivo == NULL) {
                printf("Erro, nao foi possivel abrir o arquivo\n");
            }
            else {
                for (frequencia = freqInicial; frequencia <= freqFinal; frequencia += passo) {
                    //nBJTs=0;
                    montaEstampaAC();
                    resolversistemaAC();

                    fprintf(arquivo, "%g ", frequencia);
                    for (i = 0; i < numeroVariaveis; i++) {
                        fprintf(arquivo, "%g %g ", cabs(YnComplex[i][numeroVariaveis + 1]), (180/PI) * carg(YnComplex[i][numeroVariaveis + 1]));
                    }
                    fprintf(arquivo, "\n");
                }
            }

            fclose(arquivo);
        }
        else if (strcmp(escala, "DEC") == 0) {
            if (pontos != 0) {
                passo = 1.0 / (pontos - 1.0);
            }
            else {
                pontos = 1;
            }

            arquivo = fopen(novonome, "w");
            fprintf(arquivo, "f ");
            for (i = 0; i < numeroVariaveis; i++) {
                fprintf(arquivo, "%sm %sf ", lista[i], lista[i]);
            }
            fprintf(arquivo, "\n");

            if (arquivo == NULL) {
                printf("Erro, nao foi possivel abrir o arquivo\n");
            }

            else {
                for ( frequencia = freqInicial; frequencia <= freqFinal; frequencia *= pow(10,passo)) {
                    //nBJTs=0;
                    montaEstampaAC();
                    resolversistemaAC();

                    fprintf(arquivo, "%g ", frequencia);
                    for (i = 1; i <= numeroVariaveis; i++) {
                        fprintf(arquivo, "%g %g ", cabs(YnComplex[i][numeroVariaveis + 1]), (180/PI) * carg(YnComplex[i][numeroVariaveis + 1]));
                    }
                    fprintf(arquivo,"\n");
                }
            }

            fclose(arquivo);
        }
        else if (strcmp(escala, "OCT") == 0) {
            passo = 1.0 / (pontos - 1.0);

            arquivo = fopen(novonome, "w");
            fprintf(arquivo, "f ");
            for (i = 0; i < numeroVariaveis; i++) {
                fprintf(arquivo, "%sm %sf ", lista[i], lista[i]);
            }
            fprintf(arquivo, "\n");

            if (arquivo == NULL) {
                printf("Erro, nao foi possivel abrir o arquivo\n");
            }
            else {
                for (frequencia = freqInicial; frequencia <= freqFinal; frequencia *= pow(2,passo)) {
                    //nBJTs=0;
                    montaEstampaAC();
                    resolversistemaAC();

                    fprintf(arquivo, "%g ", frequencia);
                    for (i = 1; i <= numeroVariaveis; i++) {
                        fprintf(arquivo, "%g %g ", cabs(YnComplex[i][numeroVariaveis + 1]), (180/PI) * carg(YnComplex[i][numeroVariaveis + 1]));
                    }
                    fprintf(arquivo, "\n");
                }
            }

            fclose(arquivo);
        }
    }
    else if (tem == 0) {
        printf("Sistema possui apenas Ponto de Operacao\n");
        exit(1);
    }

    return 0;
}
