#include<ilcplex/cplex.h>
#include<iostream>
#include<conio.h>
#include<string.h>

#include<stdlib.h>
#include<stdio.h>
#include<math.h>
#include<cmath>
#include<time.h>

using namespace std;

#define BigM 100000

int NoProducts, NoMachines, NoLocations, NoProcess, TotMachines, TotProcess;
int *I, *L, *P, *J, *V, ***S, *C, ****A, *BestP, ***BestL, *RemainC, *LM, *SS, *TT, **PP;
int *OptBestP, ***OptBestL, *OptRemainC, *OptLM, *OptL, ***BestS;


int status, MIN, K, ****Sched, ****OptSchd,*q;
int product, machine,Counter, Sum, sum1, sum2;
int ***Location, *Process, **Machine, ***OptLocation, * OptProcess, ** OptMachine;

float cost, OptCost, init_cost;

float Fc, *B, ***T, **D, e, *interval, Rand, SUM;
float **Z1, **Z2, **Z, *Zp, val, alfa;

int NOShips,NOChambers,*Capacity,*lockagetime,*arriveltime,STarttime,**GamaU,**GamaD;
int	CPXnv,CounterRows = 0;
float Coverage_Radius, Coverage_Radius_0, StartTime, EndTime, zarib, TotalCost;

double objval;
double gap_p;
char FileName[100] , Iname[100];

int i , j , k , l , m , n , o , p, iii , jjj , kkk , lll , mmm, a, b, c;


FILE *Input , *Output , *out;

int i1 , i2 , i3;

CPXENVptr env = NULL;
CPXLPptr  lp  = NULL;
CPXFILEptr logfile;
double *slack;
int	    STATUS, status1, counter;
char    errmsg[1024];
int		*rmatind, *rmatbeg;
char	*sense, *coltype, **colname;
long	constraints,nzcnt,numcols,numrows;
long	*YPtr , **XPtr , ***ZPtr , ***UPtr, ****RPtr;
long    d1plus , d1minus, d2plus , d2minus;

double	*rhs, *rmatval, *obj, *lb,*ub, *X_Cplex;
short int CPXEnv;

float second() { 
	return((float )clock()/(float)CLK_TCK);
}

int Partition (int lower , int upper)
{
	int x , t ;
	int tempe[2];
	tempe[0] = 0;
	x = SS[upper];
	i = lower-1;
	for (int j=lower ; j < upper; j++  )
	{
		if (SS[j] <= x)
		{
			i++;
			t = SS[i];
			tempe[0] = TT[i];
			SS [i] = SS[j];
			TT[i] = TT[j];
			SS[j] = t;
			TT[j] = tempe[0];
			
		}
	}
	t = SS[++i];
	tempe[0] = TT[i];
	SS[i] = SS[upper];
	TT[i] = TT[upper];
	SS[upper] = t;
	TT[upper] = tempe[0];
	return i;
}

void quicksort(int a , int b){
	int q;
	if ( a < b)
	{
		q = Partition (a , b);
		quicksort(a, q-1);
		quicksort(q+1 , b);
	}
}


void ReadData (){
	
	fscanf(Input,"%d",&NoProducts);
	fscanf(Input,"%d",&NoMachines);
	fscanf(Input,"%d",&NoLocations);

	fscanf(Input,"%f",&Fc);

	V = new int [NoProducts + 1];
	for(j=1;j<NoProducts+1;j++)
		fscanf(Input,"%d",&V[j]);

	I = new int [NoProducts + 1];
	for(j=1;j<NoProducts+1;j++)
		fscanf(Input,"%d",&I[j]);

	L = new int [NoLocations + 1];
	for(j=1;j<NoLocations+1;j++)
		L[j] = 0;

	LM = new int [NoLocations + 1];
	for(j=1;j<NoLocations+1;j++)
		LM[j] = 0;

	OptL = new int[NoLocations + 1];
	OptLM = new int[NoLocations + 1];
	
	q = new int[NoProducts + NoMachines + 1];

	P = new int [NoProducts + 1];
	for(j=1;j<NoProducts+1;j++)
		P[j] = 0;
	
	
	S = new int **[NoProducts+1];
	for (i=1;i < NoProducts+1;i++){
		S[i]= new int *[I[i]+1];
		for(j=0;j<I[i]+1;j++)
			S[i][j] = new int [NoMachines+1];
	}

	for(i=1;i<NoProducts+1;i++){
		for(j=1;j<I[i]+1;j++){
			fscanf(Input,"%d",&S[i][j][0]);
		}
	}
	for(i=1;i<NoProducts+1;i++){
		for(j=1;j<I[i]+1;j++){
			for(k=1;k<S[i][j][0]+1;k++)
				fscanf(Input,"%d",&S[i][j][k]);
		}
	}

	T = new float **[NoProducts+1];
	for (i=1;i < NoProducts+1;i++){
		T[i]= new float *[I[i]+1];
		for(j=1;j<I[i]+1;j++)
			T[i][j] = new float [S[i][j][0]+1];
	}

	for(i=1;i<NoProducts+1;i++){
		for(j=1;j<I[i]+1;j++){
			for(k=1;k<S[i][j][0]+1;k++)
				fscanf(Input,"%f",&T[i][j][k]);
		}
	}
	
	J = new int [NoMachines + 1];
	for(j=1;j<NoMachines+1;j++)
		fscanf(Input,"%d",&J[j]);

	C = new int [NoMachines + 1];
	for(j=1;j<NoMachines+1;j++)
		fscanf(Input,"%d",&C[j]);
	

	B = new float [NoMachines + 1];
	for(j=1;j<NoMachines+1;j++)
		fscanf(Input,"%f",&B[j]);

	D = new float *[NoLocations+1];
	for(i=0;i<NoLocations+1;i++)
		D[i] = new float [NoLocations+1];

	for(i=1;i<NoLocations+1;i++){
		for(j=1;j<NoLocations+1;j++){
			fscanf(Input,"%f",&D[i][j]);
		}
	}

	RemainC = new int [NoLocations+1];
	for(i=1;i<NoLocations+1;i++)
		RemainC[i] = 0;

	

	OptRemainC = new int[NoLocations + 1];
	A = new int ***[NoProducts+1];
	for (i=1;i < NoProducts+1;i++){
		A[i]= new int **[I[i]+1];
		for(j=0;j<I[i]+1;j++){
			A[i][j] = new int *[NoMachines+1];
			for(k=0;k<NoMachines+1;k++)
				A[i][j][k] = new int [NoMachines+1];
		}
	}

	for(i=1;i<NoProducts+1;i++){
		for(j=1;j<I[i]+1;j++){
			for(k=1;k<NoMachines+1;k++){
				for(l=1;l<NoMachines+1;l++)			
					A[i][j][k][l] = 0;
			}
		}
	}

	for(i=1;i<NoProducts+1;i++){
		for(j=1;j<I[i]+1;j++){
			for(k=1;k<S[i][j][0];k++){		
				A[i][j][S[i][j][k]][S[i][j][k+1]] = 1;
			}
		}
	}

	Z = new float *[NoProducts+1];
	for (i=1;i < NoProducts+1;i++)
		Z[i]= new float [I[i]+1];

	Z1 = new float *[NoProducts+1];
	for (i=1;i < NoProducts+1;i++)
		Z1[i]= new float [I[i]+1];

	Z2 = new float *[NoProducts+1];
	for (i=1;i < NoProducts+1;i++)
		Z2[i]= new float [I[i]+1];

	for(i=1;i<NoProducts+1;i++){
		for(j=1;j<I[i]+1;j++)
			Z2[i][j] = 0;
	}

	for(i=1;i<NoProducts+1;i++){
		for(j=1;j<I[i]+1;j++){
			for(k=1;k<S[i][j][0]+1;k++)
			Z2[i][j] += B[S[i][j][k]];
		}
	}


	BestL = new int **[NoProducts+1];
	for (i=1;i < NoProducts+1;i++){
		BestL[i]= new int *[I[i]+1];
		for(j=1;j<I[i]+1;j++)
			BestL[i][j] = new int [S[i][j][0]+1];
	}

	BestP = new int [NoProducts+1];
	Zp = new float [NoProducts+1];

	
	OptBestL = new int** [NoProducts + 1];
	for (i = 1; i < NoProducts + 1; i++) {
		OptBestL[i] = new int* [I[i] + 1];
		for (j = 1; j < I[i] + 1; j++)
			OptBestL[i][j] = new int[S[i][j][0] + 1];
	}

	OptBestP = new int[NoProducts + 1];


	Sched = new int ***[NoProducts+1];
	for (i=1;i < NoProducts+1;i++){
		Sched[i]= new int **[I[i]+1];
		for(j=1;j<I[i]+1;j++){
			Sched[i][j] = new int *[S[i][j][0]+1];
			for(k=1;k<S[i][j][0]+1;k++)
				Sched[i][j][k] = new int [NoLocations+1];
		}
	}

	OptSchd = new int*** [NoProducts + 1];
	for (i = 1; i < NoProducts + 1; i++) {
		OptSchd[i] = new int** [I[i] + 1];
		for (j = 1; j < I[i] + 1; j++) {
			OptSchd[i][j] = new int* [S[i][j][0] + 1];
			for (k = 1; k < S[i][j][0] + 1; k++)
				OptSchd[i][j][k] = new int[NoLocations + 1];
		}
	}

	Location = new int **[NoLocations+1];
	for (i=0;i < NoLocations+1;i++){
		Location[i]= new int *[NoProducts+1];
		for(j=0;j<NoProducts+1;j++){
			Location[i][j] = new int [3];
		}
	}
	
	Process = new int [NoProducts+1];

	Machine = new int *[NoProducts+1];
	for (i=0;i < NoProducts+1;i++){
		Machine[i]= new int [NoMachines+1];
	}

	OptLocation = new int** [NoLocations + 1];
	for (i = 0; i < NoLocations + 1; i++) {
		OptLocation[i] = new int* [NoProducts + 1];
		for (j = 0; j < NoProducts + 1; j++) {
			OptLocation[i][j] = new int[3];
		}
	}

	OptProcess = new int[NoProducts + 1];

	OptMachine = new int* [NoProducts + 1];
	for (i = 0; i < NoProducts + 1; i++) {
		OptMachine[i] = new int[NoMachines + 1];
	}

	PP = new int* [NoProducts + 1];
	for (i = 0; i < NoProducts + 1; i++) {
		PP[i] = new int[2];
	}

}

void SWAP(){
	for(i=1;i<NoProducts;i++){
		for(j=i+1;j<NoProducts+1;j++){
			
			for(k=1;k<S[i][Process[i]][0]+1;k++){
				for(l=1;l<S[j][Process[j]][0]+1;l++){
					if(S[i][Process[i]][k] != S[j][Process[j]][l] || Machine[i][k] == Machine[j][l])
						continue;

					a = Machine[i][k];
					b = Machine[j][l];
					m = S[i][Process[i]][k];

					if( ((RemainC[a] + T[i][Process[i]][k]*V[i]) < T[j][Process[j]][l]*V[j]) || ((RemainC[b] + T[j][Process[j]][l]*V[j]) < T[i][Process[i]][k]*V[i]))
						continue;

					sum1 = 0;
					sum2 = 0;
					if(k != 1){
						sum1 += D[Machine[i][k-1]][a] * V[i];
						sum2 += D[Machine[i][k-1]][b] * V[i];
					}

					if(k != S[i][Process[i]][0]){
						sum1 += D[a][Machine[i][k+1]] * V[i];
						sum2 += D[b][Machine[i][k+1]] * V[i];
					}

					if(l != 1){
						sum1 += D[Machine[j][l-1]][b] * V[j];
						sum2 += D[Machine[j][l-1]][a] * V[j];
					}

					if(l != S[j][Process[j]][0]){
						sum1 += D[b][Machine[j][l+1]] * V[j];
						sum2 += D[a][Machine[j][l+1]] * V[j];
					}

					if(sum1 > sum2)
						p = 0;
				}
			}
		}
	}
}

void EX_INS(){
	
	for(i=1;i<NoProducts;i++){
		for(j=1;j<S[i][Process[i]][0]+1;j++){
			for(k=1;k<NoLocations+1;k++){
				if(Machine[i][j] == k || (S[i][Process[i]][j] != LM[k] && LM[k] != 0))
					continue;

				if(LM[k] != 0 && RemainC[k] < V[i]*T[i][Process[i]][j])
					continue;
				
				a = Machine[i][j];

				sum1 = 0;
				sum2 = 0;

				if(j != 1){
					sum1 += D[Machine[i][j-1]][a] * V[i];
					sum2 += D[Machine[i][j-1]][k] * V[i];
				}

				if(j != S[i][Process[i]][0]){
					sum1 += D[a][Machine[i][j+1]] * V[i];
					sum2 += D[k][Machine[i][j+1]] * V[i];
				}

				if(LM[k] == 0)
					sum2 += B[S[i][Process[i]][j]];

				if (sum1 > sum2 + 0.01) {

					cost += sum2 - sum1;
					Machine[i][j] = k;

					if (Location[a][0][0] > 1) {
						for (m = 1; m <= Location[a][0][0]; m++) {
							if (Location[a][m][0] == i)
								n = m;
						}

						for (m = Location[a][0][0]; m > n; m--) {
							Location[a][m - 1][0] = Location[a][m][0];
							Location[a][m - 1][1] = Location[a][m][1];
						}
					}

					if(Location[k][0][0] == 0){
						L[k] = 1;
						LM[k] = S[i][Process[i]][j];
					}



					Location[a][0][0] --;

					if(Location[k][0][0] == 0)
						RemainC[k] = C[S[i][Process[i]][j]] - T[i][Process[i]][j] * V[i];

					else
						RemainC[k] = RemainC[k] - T[i][Process[i]][j] * V[i];

					if (Location[a][0][0] > 0)
						RemainC[a] = RemainC[a] + T[i][Process[i]][j] * V[i];

					Sched[i][Process[i]][j][a] = 0;
					Sched[i][Process[i]][j][k] = 1;

					Location[k][0][0]++;
					Location[k][Location[k][0][0]][0] = i;
					Location[k][Location[k][0][0]][1] = Process[i];
					Location[k][Location[k][0][0]][2] = S[i][Process[i]][j];
				}
					
			}

		}
	}
}
/*
void Separation(){

	////

}

void Integration(){
	
}
*/
void Define_Array(){
	NoMachines = 10;
	NoLocations = 100;


	XPtr = new long *[NoMachines+1];
	for (i=0;i < NoMachines+1;i++){
		XPtr[i]= new long [NoLocations+1];
	}

	
	
	RPtr = new long ***[NoMachines+1];
	for(k=0;k<NoMachines+1;k++){
		RPtr[k] = new long **[NoMachines+1];
		for(l=0;l<NoMachines+1;l++){
			RPtr[k][l] = new long *[NoLocations+1];
			for(m=0;m<NoLocations+1;m++){
				RPtr[k][l][m] = new long [NoLocations+1];
				
			}
		}
	}
	
	rhs	= new double [2];
	
	rmatval	= new double [1000000 + 85000];
	
	rmatind	  = new int [1000000 + 85000];
	
	rmatbeg	  = new int [2];
	
	sense	  = new char [2];
	
	obj	  = new double [1000000 + 85000];
	
	lb	  = new double [1000000 + 85000];
	
	ub	  = new double [1000000 + 85000];
	
	coltype = new char   [1000000 + 85000];
	
	colname = new char  *[1000000 + 85000];
	for (i = 0; i< 1000000 + 85000; i++)
		colname[i] = new char [100];


	X_Cplex = new double [4000000];

	SS = new int [NoMachines+1];
	TT = new int [NoMachines+1];

	interval = new float [NoMachines+1];
}

void Shaking() {

	for (i = 1; i < NoProducts + 1; i++) {
		q[i] = 0;
	}

	n = 0;
	q[0] = 0;
	alfa = 0.5;
	do {

		i = rand() % NoProducts + 1;
		if (Process[i] == 0)
			continue;
		
		q[0]++;
		q[q[0]] = i;

		PP[q[0]][0] = i;
		PP[q[0]][1] = Process[i];
		for (j = 1; j < S[i][Process[i]][0] + 1; j++) {
			for (l = 1; l < NoLocations + 1; l++) {
				if (Machine[i][j] == l)
					RemainC[l] += V[i] * T[i][Process[i]][j];
			}
		}

		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0]; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					Sched[i][j][k][l] = 0;
				}
			}
		}
		

		for (j = 1; j < NoLocations + 1; j++) {
			for (k = 1; k < S[i][Process[i]][0]+1; k++) {
				if (Machine[i][k] == j && Location[j][0][0] == 1) {
					LM[j] = 0;
					L[j] = 0;
				}
			}
		}
		
		for (j = 1; j < S[i][Process[i]][0] + 1; j++) {
			for (l = 1; l < NoLocations + 1; l++) {
				if (Machine[i][j] == l)
					RemainC[l] += V[i] * T[i][Process[i]][j];
			}
		}


		for (k = 1; k < NoLocations + 1; k++) {
			for (j = 1; j < S[i][Process[i]][0] + 1; j++) {

				if (Machine[i][j] != k)
					continue;

				if (Location[k][0][0] > 1) {
					for (m = 1; m <= Location[k][0][0]; m++) {
						if (Location[k][m][0] == i)
							n = m;
					}

					for (m = Location[k][0][0]; m > n; m--) {
						Location[k][m - 1][0] = Location[k][m][0];
						Location[k][m - 1][1] = Location[k][m][1];
					}
				}



				Location[k][0][0] --;
			}
		}


		for (j = 1; j < S[i][Process[i]][0] + 1; j++)
			Machine[i][j] = 0;
		
		Process[i] = 0;


	} while (((q[0] * 1.0) / NoProducts) < alfa);

	status = rand() % 2;
	status = 0;
	if(status == 1)
		EX_INS();

	n = 0;
	do {
		
		k = rand() % q[0] + 1;
		if (Process[PP[k][0]] != 0)
			continue;

		i = PP[k][0];
		if (I[i] > 1) {
			j = 0;
			do {
				p = rand() % I[i] + 1;
				if (p == PP[k][1])
					continue;

				j = 1;
			} while (j == 0);
		}

		else
			p = 1;

		Process[i] = p;

		status = rand() % 2;
		status = 1;
		///Status Assign
		SUM = 1000000000;
		Sum = SUM + 1;
		if (status == 1) {
			for (k = 1; k < NoLocations + 1; k++) {
				if ((LM[k] > 0 && LM[k] != S[i][p][1]) || (RemainC[k] < T[i][p][1]*V[i] && LM[k] > 0))
					continue;

				if (S[i][p][0] > 1) {
					for (l = 1; l < NoLocations + 1; l++) {
						if (k == l || (LM[l] > 0 && LM[l] != S[i][p][2]) || RemainC[l] < T[i][p][2] * V[i])
							continue;

						if (LM[k] > 0) {
							if(LM[l] > 0)
								Sum = D[k][l] * T[i][p][1] * V[i];

							else
								Sum = B[S[i][p][2]] + D[k][l] * T[i][p][1] * V[i];
						}

						else {
							if (LM[l] > 0)
								Sum = B[S[i][p][1]] + D[k][l] * T[i][p][1] * V[i];

							else
								Sum = B[S[i][p][1]] + B[S[i][p][2]] + D[k][l] * T[i][p][1] * V[i];
						}

						if (Sum < SUM) {
							SUM = Sum;
							a = k;
							b = l;
						}
					}
				}

				else {
					if(LM[k] == 0){
						if (B[S[i][p][1]] < SUM) {
							SUM = B[S[i][p][1]];
							a = k;
						}
					}

					else {
						SUM = 0;
						a = k;
					}
				}
			}

			if(LM[a] == 0)
				RemainC[a] = C[S[i][p][1]] - T[i][p][1] * V[i];

			else
				RemainC[a] = RemainC[a] - T[i][p][1] * V[i];
			L[a] = 1;
			LM[a] = S[i][p][1];
			
			Location[a][0][0]++;
			Location[a][Location[a][0][0]][0] = i;
			Location[a][Location[a][0][0]][1] = p;
			Location[a][Location[a][0][0]][2] = S[i][p][1];

			Machine[i][1] = a;
			Sched[i][p][1][a] = 1;

			if (S[i][p][0] > 1) {
				if (LM[b] == 0)
					RemainC[b] = C[S[i][p][2]] - T[i][p][2] * V[i];

				else
					RemainC[b] = C[S[i][p][2]] - T[i][p][2] * V[i];

				L[b] = 1;
				LM[b] = S[i][p][2];

				Location[b][0][0]++;
				Location[b][Location[b][0][0]][0] = i;
				Location[b][Location[b][0][0]][1] = p;
				Location[b][Location[b][0][0]][2] = S[i][p][2];
				
				Machine[i][2] = b;
				Sched[i][p][2][b] = 1;
			}
			

			m = 2;
			while (m < S[i][p][0]) {

				MIN = 1000000000;
				for (k = 1; k < NoLocations + 1; k++) {
					if (k == b || (L[k] == 1 && LM[k] != S[i][p][m+1]) || (LM[k] == S[i][p][m + 1] && RemainC[k] < T[i][p][m+1] * V[i]))
						continue;

					if (L[k] == 0 && (B[S[i][p][m + 1]] + D[b][k] * T[i][p][m + 1] * V[i]) < MIN) {
						MIN = B[S[i][p][m + 1]] + D[b][k] * T[i][p][m + 1] * V[i];
						a = k;
					}
					
					if (L[k] > 0 && (D[b][k] * T[i][p][m + 1] * V[i]) < MIN) {
						MIN = D[b][k] * T[i][p][m + 1] * V[i];
						a = k;
					}
				}

				m++;
				b = a;

				if(L[b] > 0)
					RemainC[b] = RemainC[b] - T[i][p][m] * V[i];
				else
					RemainC[b] = C[S[i][p][m]] - T[i][p][m] * V[i];


				L[b] = 1;
				LM[b] = S[i][p][m];
				Location[b][0][0] ++;
				Location[b][Location[b][0][0]][0] = i;
				Location[b][Location[b][0][0]][1] = p;
				Location[b][Location[b][0][0]][2] = S[i][p][m];

				Machine[i][m] = b;
				Sched[i][p][m][b] = 1;

			}

		}
		///End Status

		n++;
	} while (n < q[0]);
	
	cost = 0;
	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0]; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					for (m = 1; m < NoLocations + 1; m++) {
						cost += Fc * Sched[i][j][k][l] * Sched[i][j][k + 1][m] * D[l][m] * V[i];
					}
				}
			}
		}
	}

	B[0] = 0;
	for (i = 1; i < NoLocations + 1; i++)
		cost += B[LM[i]];

	i = 0;

	/*
	for (l = 1; l < NoLocations + 1; l++) {
		for (i = 1; i < NoProducts + 1; i++) {
			for (j = 1; j < I[i] + 1; j++) {
				for (k = 1; k < S[i][j][0]+1; k++) {
					if(Sched[i][j][k][l] == 1)
						fprintf(out, "%d:%d-%d-%d\n", l,i,j,k);
				}
			}
		}
		fprintf(out, "\n");
	}
	
	fflush(out);*/
	i = 0;

}

void Initial_Solution_II() {

	TotalCost = 0;
	for (l = 1; l < NoLocations + 1; l++) {
		for (i = 0; i < NoProducts + 1; i++) {
			for (j = 0; j < 3; j++) {
				Location[l][i][j] = 0;
			}
		}
	}

	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0] + 1; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					Sched[i][j][k][l] = 0;
				}
			}
		}
	}

	for (i = 1; i < NoProducts + 1; i++)
		Process[i] = 0;

	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 0; j < NoMachines + 1; j++)
			Machine[i][j] = 0;
	}

	p = rand() % NoProducts + 1;
	MIN = 1000000000;
	Sum = 0;
	SUM = 0;
	for (j = 1; j < I[p] + 1; j++) {
		SS[j] = 0;
		for (k = 1; k < S[p][j][0] + 1; k++) {
			SS[j] += T[p][j][k] * V[p];
		}

		interval[j] = 1.0 / float(SS[j]);
		SUM += interval[j];
		/*
		if(n < MIN){
			MIN = n;
			i = j;
		}*/
	}

	interval[0] = 0;
	for (j = 1; j < I[p] + 1; j++)
		interval[j] = interval[j - 1] + interval[j] / SUM;

	Rand = second() * 3045.56486;
	Rand = Rand - int(Rand);
	for (j = 1; j < I[p] + 1; j++) {
		if (Rand <= interval[j]) {
			i = j;
			break;
		}
	}

	i = rand() % I[p] + 1;

	Process[p] = i;
	MIN = 1000000000;
	for (k = 1; k < NoLocations + 1; k++) {
		for (l = 1; l < NoLocations + 1; l++) {

			if (k == l)
				continue;

			if (D[k][l] < MIN) {
				MIN = D[k][l];
				a = k;
				b = l;
			}
		}
	}

	L[a] = 1;
	L[b] = 1;

	LM[a] = S[p][i][1];
	LM[b] = S[p][i][2];

	Location[a][0][0] = 1;
	Location[a][1][0] = p;
	Location[a][1][1] = i;
	Location[a][1][2] = S[p][i][1];

	Location[b][0][0] = 1;
	Location[b][1][0] = p;
	Location[b][1][1] = i;
	Location[b][1][2] = S[p][i][2];

	RemainC[a] = C[S[p][i][1]] - T[p][i][1] * V[p];
	RemainC[b] = C[S[p][i][2]] - T[p][i][2] * V[p];

	Machine[p][1] = a;
	Machine[p][2] = b;

	Sched[p][i][1][a] = 1;
	Sched[p][i][2][b] = 1;

	m = 2;
	while (m < S[p][i][0]) {

		MIN = 1000000000;
		for (k = 1; k < NoLocations + 1; k++) {
			if (k == b || L[k] == 1)
				continue;

			if (D[b][k] < MIN) {
				MIN = D[b][k];
				a = k;
			}
		}

		m++;
		b = a;
		L[b] = 1;
		LM[b] = S[p][i][m];

		Location[b][0][0] = 1;
		Location[b][1][0] = p;
		Location[b][1][1] = i;
		Location[b][1][2] = S[p][i][m];

		RemainC[b] = C[S[p][i][m]] - T[p][i][m] * V[p];

		Machine[p][m] = b;
		Sched[p][i][m][b] = 1;

	}

	n = 1;
	do {
		Sum = 0;
		MIN = 1000000000;

		//do{
			//j = rand() % NoProducts + 1;
		for (j = 1; j < NoProducts + 1; j++) {
			if (Process[j] != 0)
				continue;

			for (l = 1; l < I[j] + 1; l++) {
				Sum = 0;
				for (m = 1; m < S[j][l][0] + 1; m++) {
					status = 0;
					for (k = 1; k < NoLocations + 1; k++) {
						if (LM[k] == S[j][l][m] && RemainC[k] >= V[j] * T[j][l][m]) {
							status = 1;
							break;
						}
					}

					if (status == 0)
						Sum += B[S[j][l][m]];
				}

				if (Sum < MIN) {
					p = j;
					i = l;
					MIN = Sum;
				}
			}
		}

		p = rand() % NoProducts + 1;
		if (Process[p] > 0)
			continue;

		i = rand() % I[p] + 1;

		Process[p] = i;
		status = 0;

		for (m = 1; m < S[p][i][0] + 1; m++)
			q[m] = 0;
		
		for (m = 1; m < S[p][i][0] + 1; m++) {
			for (k = 1; k < NoLocations + 1; k++) {
				if (LM[k] == S[p][i][m] && RemainC[k] >= V[p] * T[p][i][m] && q[m] == 0) {

					Location[k][0][0]++;
					Location[k][Location[k][0][0]][0] = p;
					Location[k][Location[k][0][0]][1] = i;
					Location[k][Location[k][0][0]][2] = S[p][i][m];

					Machine[p][m] = k;

					RemainC[k] = RemainC[k] - T[p][i][m] * V[p];

					Sched[p][i][m][k] = 1;
					
					q[m] = 1;

					status = 1;
				}
			}
		}

		//status = 0;

		//////if//////
		if (status == 1) {
			STATUS = 0;
			for (m = 1; m < S[p][i][0] + 1; m++) {
				for (k = 1; k < NoLocations + 1; k++) {
					if (LM[k] == S[p][i][m] && Machine[p][m] > 0) {
						i1 = m;
						STATUS = 1;
						break;
					}
				}
				if (STATUS == 1)
					break;
			}
			j = i1;
			for (m = i1 - 1; m > 0; m--) {
				MIN = 100000000;
				for (l = 1; l < NoLocations + 1; l++) {
					if (L[l] == 1)
						continue;

					if (D[l][Machine[p][j]] < MIN) {
						k = l;
						MIN = D[l][Machine[p][j]];
					}
				}

				L[k] = 1;
				LM[k] = S[p][i][m];

				Location[k][0][0] = 1;
				Location[k][1][0] = p;
				Location[k][1][1] = i;
				Location[k][1][2] = S[p][i][m];

				Machine[p][m] = k;

				RemainC[k] = C[S[p][i][m]] - T[p][i][m] * V[p];

				Sched[p][i][m][k] = 1;
				j = m;
			}


			STATUS = 0;
			for (m = S[p][i][0]; m > 0; m--) {
				for (k = 1; k < NoLocations + 1; k++) {
					if (LM[k] == S[p][i][m] && Machine[p][m] > 0) {
						i2 = m;
						STATUS = 1;
						break;
					}
				}
				if (STATUS == 1)
					break;
			}

			j = i2;
			for (m = i1 + 1; m < S[p][i][0] + 1; m++) {
				MIN = 100000000;
				for (l = 1; l < NoLocations + 1; l++) {
					if (L[l] == 1)
						continue;

					if (D[Machine[p][j]][l] < MIN) {
						k = l;
						MIN = D[l][Machine[p][j]];
					}
				}

				L[k] = 1;
				LM[k] = S[p][i][m];

				Location[k][0][0] = 1;
				Location[k][1][0] = p;
				Location[k][1][1] = i;
				Location[k][1][2] = S[p][i][m];

				Machine[p][m] = k;

				RemainC[k] = C[S[p][i][m]] - T[p][i][m] * V[p];

				Sched[p][i][m][k] = 1;
				j = m;
			}

			for (m = i1 + 1; m < i2; m++) {
				if (Machine[p][m] > 0)
					continue;

				MIN = 100000000;
				for (l = 1; l < NoLocations + 1; l++) {
					if (L[l] == 1)
						continue;

					if (D[Machine[p][m - 1]][l] < MIN) {
						k = l;
						MIN = D[Machine[p][m - 1]][l];
					}
				}

				L[k] = 1;
				LM[k] = S[p][i][m];

				Location[k][0][0] = 1;
				Location[k][1][0] = p;
				Location[k][1][1] = i;
				Location[k][1][2] = S[p][i][m];

				Machine[p][m] = k;

				RemainC[k] = C[S[p][i][m]] - T[p][i][m] * V[p];

				Sched[p][i][m][k] = 1;
			}
		}
		//////endif//////


		///////else//////
		else {

			MIN = 1000000000;
			for (k = 1; k < NoLocations + 1; k++) {
				for (l = 1; l < NoLocations + 1; l++) {

					if (k == l || L[k] == 1 || L[l] == 1)
						continue;

					if (D[k][l] < MIN) {
						MIN = D[k][l];
						a = k;
						b = l;
					}
				}
			}

			L[a] = 1;
			L[b] = 1;

			LM[a] = S[p][i][1];
			LM[b] = S[p][i][2];

			Location[a][0][0] = 1;
			Location[a][1][0] = p;
			Location[a][1][1] = i;
			Location[a][1][2] = S[p][i][1];

			Location[b][0][0] = 1;
			Location[b][1][0] = p;
			Location[b][1][1] = i;
			Location[b][1][2] = S[p][i][2];

			RemainC[a] = C[S[p][i][1]] - T[p][i][1] * V[p];
			RemainC[b] = C[S[p][i][2]] - T[p][i][2] * V[p];

			Machine[p][1] = a;
			Machine[p][2] = b;

			Sched[p][i][1][a] = 1;
			Sched[p][i][2][b] = 1;

			m = 2;
			while (m < S[p][i][0]) {

				MIN = 1000000000;
				for (k = 1; k < NoLocations + 1; k++) {
					if (k == b || L[k] == 1)
						continue;

					if (D[b][k] < MIN) {
						MIN = D[b][k];
						a = k;
					}
				}

				m++;
				b = a;
				L[b] = 1;
				LM[b] = S[p][i][m];

				Location[b][1][0] = p;
				Location[b][1][1] = i;
				Location[b][1][2] = S[p][i][m];

				RemainC[b] = C[S[p][i][m]] - T[p][i][m] * V[p];

				Machine[p][m] = b;
				Sched[p][i][m][b] = 1;

			}
		}
		////endelse/////
		n++;
	} while (n < NoProducts);

	cost = 0;
	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0]; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					for (m = 1; m < NoLocations + 1; m++) {

						cost += Fc * Sched[i][j][k][l] * Sched[i][j][k + 1][m] * D[l][m] * V[i];
					}
				}
			}
		}
	}
	//EX_INS();
	/*for (l = 1; l < NoLocations + 1; l++) {
		for (i = 1; i < NoProducts + 1; i++) {
			for (j = 1; j < I[i] + 1; j++) {
				for (k = 1; k < S[i][j][0] + 1; k++) {
					if (Sched[i][j][k][l] == 1)
						fprintf(out, "%d:%d-%d-%d\n", l, i, j, k);
				}
			}
		}
		fprintf(out, "\n");
	}

	fflush(out);*/

	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0]; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					OptSchd[i][j][k][l] = Sched[i][j][k][l];
				}
			}
		}
	}

	for (j = 1; j < NoLocations + 1; j++) {
		OptL[j] = L[j];
		OptLM[j] = LM[j];
	}

	for (i = 1; i < NoLocations + 1; i++) {
		OptRemainC[i] = RemainC[i];
	}

	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0] + 1; k++)
				OptBestL[i][j][k] = BestL[i][j][k];
		}
	}

	for (i = 1; i < NoProducts + 1; i++) {
		OptBestP[i] = BestP[i];
		OptProcess[i] = Process[i];
	}

	for (i = 0; i < NoLocations + 1; i++) {
		for (j = 0; j < NoProducts + 1; j++) {
			for (k = 0; k < 3; k++)
				OptLocation[i][j][k] = Location[i][j][k];
		}
	}


	for (i = 0; i < NoProducts + 1; i++) {
		for (j = 0; j < NoMachines + 1; j++)
			OptMachine[i][j] = Machine[i][j];
	}



	//SWAP();
	//EX_INS();

	cost = 0;
	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0]; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					for (m = 1; m < NoLocations + 1; m++) {
						cost += Fc * Sched[i][j][k][l] * Sched[i][j][k + 1][m] * D[l][m] * V[i];
					}
				}
			}
		}
	}

	B[0] = 0;
	for (i = 1; i < NoLocations + 1; i++)
		cost += B[LM[i]];


	OptCost = cost;
	init_cost = cost;
	i = 0;
	//Shaking ();
}

void Initial_Solution(){
	
	TotalCost = 0;
	for(l=1;l<NoLocations+1;l++){
		for(i=0;i<NoProducts+1;i++){
			for(j=0;j<3;j++){
				Location[l][i][j] = 0;
			}
		}
	}

	for(i=1;i<NoProducts+1;i++){
		for(j=1;j<I[i]+1;j++){
			for(k=1;k<S[i][j][0]+1;k++){
				for(l=1;l<NoLocations+1;l++){
					Sched[i][j][k][l] = 0;
				}
			}
		}
	}

	for(i=1;i<NoProducts+1;i++)
		Process[i] = 0;

	for(i=1;i<NoProducts+1;i++){
		for(j=0;j<NoMachines+1;j++)
			Machine[i][j] = 0;
	}

	p = rand() % NoProducts + 1;
	MIN = 1000000000;		
	Sum = 0;
	SUM = 0;
	for(j=1;j<I[p]+1;j++){
		SS[j] = 0;
		for(k=1;k<S[p][j][0]+1;k++){
			SS[j] += T[p][j][k]*V[p];
		}

		interval[j] = 1.0 / float(SS[j]);
		SUM += interval[j];
		/*
		if(n < MIN){
			MIN = n;
			i = j;
		}*/
	}

	interval[0] = 0;
	for(j=1;j<I[p]+1;j++)
		interval[j] = interval[j-1] + interval[j] /SUM;

	Rand = second()*3045.56486;
	Rand = Rand - int(Rand);
	for(j=1;j<I[p]+1;j++){
		if(Rand <= interval[j]){
			i = j;
			break;
		}
	}


	Process[p] = i;
	MIN = 1000000000;
	for(k=1;k<NoLocations+1;k++){
		for(l=1;l<NoLocations+1;l++){

			if(k == l)
				continue;

			if(D[k][l] < MIN){
				MIN = D[k][l];
				a = k;
				b = l;
			}
		}
	}

	L[a] = 1;
	L[b] = 1;

	LM[a] = S[p][i][1];
	LM[b] = S[p][i][2];

	Location[a][0][0] = 1;
	Location[a][1][0] = p;
	Location[a][1][1] = i;
	Location[a][1][2] = S[p][i][1];

	Location[b][0][0] = 1;
	Location[b][1][0] = p;
	Location[b][1][1] = i;
	Location[b][1][2] = S[p][i][2];

	RemainC[a] = C[S[p][i][1]] - T[p][i][1]*V[p];
	RemainC[b] = C[S[p][i][2]] - T[p][i][2]*V[p];

	Machine[p][1] = a;
	Machine[p][2] = b;

	Sched[p][i][1][a] = 1;
	Sched[p][i][2][b] = 1;

	m = 2;
	while(m < S[p][i][0]){

		MIN = 1000000000;
		for(k=1;k<NoLocations+1;k++){
			if(k == b|| L[k] == 1)
				continue;

			if(D[b][k] < MIN){
				MIN = D[b][k];
				a = k;
			}
		}

		m++;
		b = a;
		L[b] = 1;
		LM[b] = S[p][i][m];
		
		Location[b][0][0] = 1;
		Location[b][1][0] = p;
		Location[b][1][1] = i;
		Location[b][1][2] = S[p][i][m];			

		RemainC[b] = C[S[p][i][m]] - T[p][i][m]*V[p];

		Machine[p][m] = b;
		Sched[p][i][m][b] = 1;
		
	}

	n = 1;
	do{
		Sum = 0;
		MIN = 1000000000;

		//do{
			//j = rand() % NoProducts + 1;
		for(j=1;j<NoProducts+1;j++){
			if(Process[j] != 0)
				continue;

			for(l=1;l<I[j]+1;l++){
				Sum = 0;
				for(m=1;m<S[j][l][0]+1;m++){
					status = 0;
					for(k=1;k<NoLocations+1;k++){
						if(LM[k] == S[j][l][m] && RemainC[k] >= V[j]*T[j][l][m]){
							status = 1;
							break;
						}
					}

					if(status == 0)
						Sum += B[S[j][l][m]];
				}

				if(Sum < MIN){
					p = j;
					i = l;
					MIN = Sum;
				}
			}
		}
		Process[p] = i;
		status = 0;
		for(m=1;m<S[p][i][0]+1;m++){
			for(k=1;k<NoLocations+1;k++){
				if(LM[k] == S[p][i][m] && RemainC[k] >= V[p]*T[p][i][m]){

					Location[k][0][0]++;
					Location[k][Location[k][0][0]][0] = p;
					Location[k][Location[k][0][0]][1] = i;
					Location[k][Location[k][0][0]][2] = S[p][i][m];

					Machine[p][m] = k;

					RemainC[k] = RemainC[k] - T[p][i][m]*V[p];

					Sched[p][i][m][k] = 1;

					status = 1;
				}
			}
		}

		//////if//////
		if(status == 1){
			STATUS = 0;
			for(m=1;m<S[p][i][0]+1;m++){
				for(k=1;k<NoLocations+1;k++){
					if(LM[k] == S[p][i][m] && Machine[p][m] > 0){
						i1 = m;
						STATUS = 1;
						break;
					}
				}
				if(STATUS == 1)
					break;
			}
			j = i1;
			for(m=i1-1;m>0;m--){
				MIN = 100000000;
				for(l=1;l<NoLocations+1;l++){
					if(L[l] == 1)
						continue;

					if(D[l][Machine[p][j]] < MIN){
						k = l;
						MIN = D[l][Machine[p][j]];
					}
				}

				L[k] = 1;
				LM[k] = S[p][i][m];

				Location[k][0][0] = 1;
				Location[k][1][0] = p;
				Location[k][1][1] = i;
				Location[k][1][2] = S[p][i][m];

				Machine[p][m] = k;

				RemainC[k] = C[S[p][i][m]] - T[p][i][m]*V[p];

				Sched[p][i][m][k] = 1;
				j = m;
			}


			STATUS = 0;
			for(m=S[p][i][0];m>0;m--){
				for(k=1;k<NoLocations+1;k++){
					if(LM[k] == S[p][i][m] && Machine[p][m] > 0){
						i2 = m;
						STATUS = 1;
						break;
					}
				}
				if(STATUS == 1)
					break;
			}

			j = i2;
			for(m=i1+1;m<S[p][i][0]+1;m++){
				MIN = 100000000;
				for(l=1;l<NoLocations+1;l++){
					if(L[l] == 1)
						continue;

					if(D[Machine[p][j]][l] < MIN){
						k = l;
						MIN = D[l][Machine[p][j]];
					}
				}

				L[k] = 1;
				LM[k] = S[p][i][m];

				Location[k][0][0] = 1;
				Location[k][1][0] = p;
				Location[k][1][1] = i;
				Location[k][1][2] = S[p][i][m];

				Machine[p][m] = k;

				RemainC[k] = C[S[p][i][m]] - T[p][i][m]*V[p];

				Sched[p][i][m][k] = 1;
				j = m;
			}

			for(m=i1+1;m<i2;m++){
				if(Machine[p][m] > 0)
					continue;
				
				MIN = 100000000;
				for(l=1;l<NoLocations+1;l++){
					if(L[l] == 1)
						continue;

					if(D[Machine[p][m-1]][l] < MIN){
						k = l;
						MIN = D[Machine[p][m-1]][l];
					}
				}

				L[k] = 1;
				LM[k] = S[p][i][m];

				Location[k][0][0] = 1;
				Location[k][1][0] = p;
				Location[k][1][1] = i;
				Location[k][1][2] = S[p][i][m];

				Machine[p][m] = k;

				RemainC[k] = C[S[p][i][m]] - T[p][i][m]*V[p];

				Sched[p][i][m][k] = 1;
			}
		}
		//////endif//////


		///////else//////
		else{

			MIN = 1000000000;
			for(k=1;k<NoLocations+1;k++){
				for(l=1;l<NoLocations+1;l++){

					if(k == l || L[k] == 1 || L[l] == 1)
						continue;

					if(D[k][l] < MIN){
						MIN = D[k][l];
						a = k;
						b = l;
					}
				}
			}

			L[a] = 1;
			L[b] = 1;

			LM[a] = S[p][i][1];
			LM[b] = S[p][i][2];

			Location[a][0][0] = 1;
			Location[a][1][0] = p;
			Location[a][1][1] = i;
			Location[a][1][2] = S[p][i][1];

			Location[b][0][0] = 1;
			Location[b][1][0] = p;
			Location[b][1][1] = i;
			Location[b][1][2] = S[p][i][2];

			RemainC[a] = C[S[p][i][1]] - T[p][i][1]*V[p];
			RemainC[b] = C[S[p][i][2]] - T[p][i][2]*V[p];

			Machine[p][1] = a;
			Machine[p][2] = b;

			Sched[p][i][1][a] = 1;
			Sched[p][i][2][b] = 1;

			m = 2;
			while(m < S[p][i][0]){

				MIN = 1000000000;
				for(k=1;k<NoLocations+1;k++){
					if(k == b|| L[k] == 1)
						continue;

					if(D[b][k] < MIN){
						MIN = D[b][k];
						a = k;
					}
				}

				m++;
				b = a;
				L[b] = 1;
				LM[b] = S[p][i][m];
		
				Location[b][1][0] = p;
				Location[b][1][1] = i;
				Location[b][1][2] = S[p][i][m];			

				RemainC[b] = C[S[p][i][m]] - T[p][i][m]*V[p];

				Machine[p][m] = b;
				Sched[p][i][m][b] = 1;
		
			}
		}
		////endelse/////
		n++;
	}while (n < NoProducts);

	cost = 0;
	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0]; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					for (m = 1; m < NoLocations + 1; m++) {
						
						cost += Fc * Sched[i][j][k][l] * Sched[i][j][k + 1][m] * D[l][m] * V[i];
					}
				}
			}
		}
	}
	
	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0]+1; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					if(Sched[i][j][k][l] == 1)
						fprintf(out, "%d\t", l);
				}
			}
		}
		fprintf(out, "\n");
	}


	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0]; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					OptSchd[i][j][k][l] = Sched[i][j][k][l];
				}
			}
		}
	}

	for (j = 1; j < NoLocations + 1; j++) {
		OptL[j] = L[j];
		OptLM[j] = LM[j];
	}

	for (i = 1; i < NoLocations + 1; i++) {
		OptRemainC[i] = RemainC[i];
	}

	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0] + 1; k++)
				OptBestL[i][j][k] = BestL[i][j][k];
		}
	}

	for (i = 1; i < NoProducts + 1; i++) {
		OptBestP[i] = BestP[i];
		OptProcess[i] = Process[i];
	}

	for (i = 0; i < NoLocations + 1; i++) {
		for (j = 0; j < NoProducts + 1; j++) {
			for (k = 0; k < 3; k++)
				OptLocation[i][j][k] = Location[i][j][k];
		}
	}


	for (i = 0; i < NoProducts + 1; i++) {
		for(j=0;j< NoMachines + 1;j++)
			OptMachine[i][j] = Machine[i][j];
	}



	//SWAP();
	//EX_INS();

	cost = 0;
	for (i = 1; i < NoProducts + 1; i++) {
		for (j = 1; j < I[i] + 1; j++) {
			for (k = 1; k < S[i][j][0]; k++) {
				for (l = 1; l < NoLocations + 1; l++) {
					for (m = 1; m < NoLocations + 1; m++) {
						cost += Fc * Sched[i][j][k][l] * Sched[i][j][k + 1][m] * D[l][m] * V[i];
					}
				}
			}
		}
	}

	B[0] = 0;
	for (i = 1; i < NoLocations + 1; i++)
		cost += B[LM[i]];


	OptCost = cost;
	i = 0;
	//Shaking ();
}

void ILS() {
	
	Counter = 0;
	StartTime = second();

	do {

		Shaking();
		do {
			TotalCost = cost;
			EX_INS();
			SWAP();
		} while (cost < TotalCost);

		
		if (cost < OptCost - 0.01) {
			cost = 0;
			for (i = 1; i < NoProducts + 1; i++) {
				for (j = 1; j < I[i] + 1; j++) {
					for (k = 1; k < S[i][j][0]; k++) {
						for (l = 1; l < NoLocations + 1; l++) {
							for (m = 1; m < NoLocations + 1; m++) {
								cost += Fc * Sched[i][j][k][l] * Sched[i][j][k + 1][m] * D[l][m] * V[i];
							}
						}
					}
				}
			}

			B[0] = 0;
			for (i = 1; i < NoLocations + 1; i++)
				cost += B[LM[i]];

			OptCost = cost;

			Counter = 0;
			for (i = 1; i < NoProducts + 1; i++) {
				for (j = 1; j < I[i] + 1; j++) {
					for (k = 1; k < S[i][j][0]; k++) {
						for (l = 1; l < NoLocations + 1; l++) {
							OptSchd[i][j][k][l] = Sched[i][j][k][l];
						}
					}
				}
			}

			for (j = 1; j < NoLocations + 1; j++) {
				OptL[j] = L[j];
				OptLM[j] = LM[j];
			}

			for (i = 1; i < NoLocations + 1; i++) {
				OptRemainC[i] = RemainC[i];
			}

			for (i = 1; i < NoProducts + 1; i++) {
				for (j = 1; j < I[i] + 1; j++) {
					for (k = 1; k < S[i][j][0] + 1; k++)
						OptBestL[i][j][k] = BestL[i][j][k];
				}
			}

			for (i = 1; i < NoProducts + 1; i++) {
				OptProcess[i] = Process[i];
			}

			for (i = 0; i < NoLocations + 1; i++) {
				for (j = 0; j < NoProducts + 1; j++) {
					for (k = 0; k < 3; k++)
						OptLocation[i][j][k] = Location[i][j][k];
				}
			}


			for (i = 0; i < NoProducts + 1; i++) {
				for (j = 0; j < NoMachines + 1; j++)
					OptMachine[i][j] = Machine[i][j];
			}
		}

		else {

			Counter ++;

			for (i = 1; i < NoProducts + 1; i++) {
				for (j = 1; j < I[i] + 1; j++) {
					for (k = 1; k < S[i][j][0]; k++) {
						for (l = 1; l < NoLocations + 1; l++) {
							Sched[i][j][k][l] = OptSchd[i][j][k][l];
						}
					}
				}
			}

			for (j = 1; j < NoLocations + 1; j++) {
				L[j] = OptL[j];
				LM[j] = OptLM[j];
			}

			for (i = 1; i < NoLocations + 1; i++) {
				RemainC[i] = OptRemainC[i];
			}

			for (i = 1; i < NoProducts + 1; i++) {
				for (j = 1; j < I[i] + 1; j++) {
					for (k = 1; k < S[i][j][0] + 1; k++)
						BestL[i][j][k] = OptBestL[i][j][k];
				}
			}

			for (i = 1; i < NoProducts + 1; i++) {
				 Process[i] = OptProcess[i];
			}

			for (i = 0; i < NoLocations + 1; i++) {
				for (j = 0; j < NoProducts + 1; j++) {
					for (k = 0; k < 3; k++)
						Location[i][j][k] = OptLocation[i][j][k];
				}
			}


			for (i = 0; i < NoProducts + 1; i++) {
				for (j = 0; j < NoMachines + 1; j++)
					Machine[i][j] = OptMachine[i][j];
			}

			cost = 0;
			for (i = 1; i < NoProducts + 1; i++) {
				for (j = 1; j < I[i] + 1; j++) {
					for (k = 1; k < S[i][j][0]; k++) {
						for (l = 1; l < NoLocations + 1; l++) {
							for (m = 1; m < NoLocations + 1; m++) {
								cost += Fc * Sched[i][j][k][l] * Sched[i][j][k + 1][m] * D[l][m] * V[i];
							}
						}
					}
				}
			}

			B[0] = 0;
			for (i = 1; i < NoLocations + 1; i++)
				cost += B[LM[i]];
			i = 0;
		}

		if (Counter > 100000)
			break;
	} while (second() - StartTime < 1000);
	
	i = 0;
}

void main (void) {


	short int CPXEnv=0;
	srand(time(0));
	for (i = 0; i < 10; i++)
		j = rand();
	

	//out = fopen("Output.txt","a");
	out = fopen("Output.txt", "w");
	Define_Array();

	for(product=4;product<=20;product++){
		for(machine=5;machine<=10;machine++){
			for(Counter=1;Counter<=5;Counter++){

				char filename[100] , Iname[100];
				TotalCost = 0;

				sprintf(Iname, "Input//Input_%d_%d_%d.txt",product,machine,Counter);
				Input = fopen(Iname, "r");

				//Input = fopen("data.txt", "r");
				if(Input == NULL)
					continue;
				CPXEnv=0;
				ReadData();
				
				Initial_Solution_II();
				//VNS();
				/*
				for (l = 1; l < NoLocations + 1; l++) {
					for (i = 1; i < NoProducts + 1; i++) {
						for (j = 1; j < I[i] + 1; j++) {
							for (k = 1; k < S[i][j][0]; k++) {
								if (OptSchd[i][j][k][l] == 1)
									fprintf(out, "%d-%d-%d-%d\n", l, i, j, k);
							}
						}
					}
				}
				fprintf(out, "\n\n\n\n");
				StartTime = second();*/
				/*
				float cost1 = 0, cost2 = 0;
				K = 0;
				do{
		
					for(i=1;i<NoProducts+1;i++){
						for(j=1;j<I[i]+1;j++)
							Z2[i][j] = 0;
					}

					for(i=1;i<NoProducts+1;i++){
						for(j=1;j<I[i]+1;j++){
							for(k=1;k<S[i][j][0]+1;k++)
							Z2[i][j] += B[S[i][j][k]];
						}
					}

					for(iii=1;iii<NoProducts+1;iii++){

						if(P[iii] == 1)
							continue;

						for(jjj=1;jjj<I[iii]+1;jjj++){
							Creat_Problem();
							ModelPopulate(iii , jjj);
							i = 0;
						}
					}

					for(i=1;i<NoProducts+1;i++){
						Zp[i] = 100000000000;
						for(j=1;j<I[i]+1;j++){
							if(Z1[i][j] + Z2[i][j] < Zp[i]){
								Zp[i] = Z1[i][j] + Z2[i][j];
								BestP[i] = j;
							}
						}
					}

					val = -1;
					for(i=1;i<NoProducts+1;i++){
						if(P[i] == 1)
							continue;

						if(Zp[i] > val){
							j = i;
							val = Zp[i];
						}
					}

					cost1 += Z1[j][BestP[j]];
					cost2 += Z2[j][BestP[j]];

					TotalCost += val;
					P[j] = 1;
					for(i=1;i<S[j][BestP[j]][0]+1;i++){

						if(BestL[j][BestP[j]][i] > 15)
							k = 0;

						L[BestL[j][BestP[j]][i]] = 1;
						LM[BestL[j][BestP[j]][i]] = S[j][BestP[j]][i];
						Sched[j][BestP[j]][i][BestL[j][BestP[j]][i]] = 1;


						if(RemainC[BestL[j][BestP[j]][i]] == 0)
							RemainC[BestL[j][BestP[j]][i]] = C[S[j][BestP[j]][i]] - V[j]*T[j][BestP[j]][i];

						else
							RemainC[BestL[j][BestP[j]][i]] = RemainC[BestL[j][BestP[j]][i]] - V[j]*T[j][BestP[j]][i];
					}

					float cost = 0;
					for(i=1;i<NoProducts+1;i++){
						for(j=1;j<I[i]+1;j++){
							for(k=1;k<S[i][j][0];k++){
								for(l=1;l<NoLocations+1;l++){
									for(m=1;m<NoLocations+1;m++){
										cost += Fc*Sched[i][j][k][l]*Sched[i][j][k+1][m]*D[l][m]*V[i];
									}
								}
							}
						}
					}

					B[0] = 0;
					for(i=1;i<NoLocations+1;i++)
						cost += B[LM[i]];


					K ++;
				}while(K < NoProducts);
				*/
				//fprintf(out, "%d\t%d\t%d\t%f\t%f\n" , product,machine,Counter,TotalCost , second() - StartTime);
				//fflush(out);
				counter = 0;
				StartTime = second();
				do {
					//Initial_Solution_II();
					Initial_Solution_II();
					if (cost < OptCost)
						OptCost = cost;
					counter++;
					fprintf(out, "%d\t%d\t%d\t%f\t%f\n", product, machine, Counter, cost, second() - StartTime);
				} while (counter < 20);/*  */
				cost = 0;
				for(i=1;i<NoProducts+1;i++){
					for(j=1;j<I[i]+1;j++){
						for(k=1;k<S[i][j][0];k++){
							for(l=1;l<NoLocations+1;l++){
								for(m=1;m<NoLocations+1;m++){
									cost += Fc*Sched[i][j][k][l]*Sched[i][j][k+1][m]*D[l][m]*V[i];
								}
							}
						}
					}
				}

				B[0] = 0;
				for(i=1;i<NoLocations+1;i++)
					cost += B[LM[i]];
	
				//fprintf(out, "%d\t%d\t%d\t%f\t%f\t%f\n", product, machine, Counter, init_cost, OptCost,second()-StartTime);
				/*for (i = 1; i < NoProducts + 1; i++) {
					for (j = 1; j < I[i] + 1; j++) {
						for (k = 1; k < S[i][j][0]+1; k++) {
							for (l = 1; l < NoLocations + 1; l++) {
								if (Sched[i][j][k][l] == 1)
									fprintf(out, "%d\t", l);
							}
						}
					}
					fprintf(out, "\n");
				}*/

				FILE* assigning;
				assigning = fopen("Solution.txt", "w");

				for (l = 1; l < NoLocations + 1; l++) {
					if (m == 1)
						fprintf(assigning, ")\t", i);
					m = 0;
					for (i = 1; i < NoProducts + 1; i++) {
						for (j = 1; j < I[i] + 1; j++) {
							for (k = 1; k < S[i][j][0]; k++) {
								if (OptSchd[i][j][k][l] == 1) {
									if (m == 1) {
										fprintf(assigning, ", %d", i);
									}

									if (m == 0) {
										m = 1;
										fprintf(assigning, "%d-%d (%d", l, S[i][j][k], i);
									}
								}

							}
						}
					}
				}

				fflush(out);
				cout << second() - StartTime << endl;
			}
		}
	}
	
}
