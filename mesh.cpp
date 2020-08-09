/**CFile****************************************************************

  FileName    [bmcMesh.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [SAT-based bounded model checking.]

  Synopsis    [Synthesis for mesh of LUTs.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: bmcMesh.c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include <iostream>
#include <algorithm>
#include <chrono>

#include <simp/SimpSolver.h>

#include "aig.hpp"

////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

#define NCPARS 16

static inline int Bmc_MeshTVar( std::vector<std::vector<int> > const & Me, int x, int y ) { return Me[x][y];                                         }
static inline int Bmc_MeshGVar( std::vector<std::vector<int> > const & Me, int x, int y ) { return Me[x][y] + Me.back()[0];                          }
static inline int Bmc_MeshCVar( std::vector<std::vector<int> > const & Me, int x, int y ) { return Me[x][y] + Me.back()[0] + Me.back()[1];           }
static inline int Bmc_MeshUVar( std::vector<std::vector<int> > const & Me, int x, int y ) { return Me[x][y] + Me.back()[0] + Me.back()[1] + NCPARS;  }

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////



/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
static inline int Bmc_MeshVarValue2( Glucose::SimpSolver * p, int v )
{
    return p->model[v] == l_True;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int integer_log2(int n) { // wrap up
  int t = 1;
  int count = 0;
  while(n > t) {
    t = t << 1;
    count++;
  }
  return count;
}
int bimander(Glucose::SimpSolver * pSat, std::vector<int> const &vVars, int nbim) {
  int nCount = 0;
  std::vector<int> vVars2;
  int m = vVars.size() / nbim + vVars.size() % nbim;
  int nb = integer_log2(m);
  int c = pSat->newVar();
  std::cout << c << std::endl;
  for(int k = 0; k < nb; k++) {
    pSat->newVar();
  }
  for(int i = 0; i < m; i++) {
    vVars2.clear();
    for(int j = 0; j < nbim && i*nbim + j < (int)vVars.size(); j++) {
      vVars2.push_back(vVars[i*nbim + j]);
    }
    if(vVars2.size() > 1) {
      // naive
      for ( int p = 0; p < vVars2.size(); p++ ) {
	for ( int q = p+1; q < vVars2.size(); q++ ) {
	  Glucose::vec<Glucose::Lit> pLits;
	  int RetValue;
	  pLits.push(Glucose::mkLit( vVars2[p], 1 ));
	  pLits.push(Glucose::mkLit( vVars2[q], 1 ));
	  RetValue = pSat->addClause(pLits);  assert( RetValue );
	  nCount++;
	}
      }
    }
    for(int k = 0; k < nb; k++) {
      int b = 1 << k;
      if(i & b) {
	for(int j = 0; j < nbim && i*nbim + j < (int)vVars.size(); j++) {
	  Glucose::vec<Glucose::Lit> pLits;
	  int RetValue;
	  pLits.push(Glucose::mkLit( vVars[i*nbim + j], 1 ));
	  pLits.push(Glucose::mkLit( c + k, 0 ));
	  std::cout << c + k << std::endl;
	  RetValue = pSat->addClause(pLits);  assert( RetValue );
	  nCount++;
	}
      }
      else {
	for(int j = 0; j < nbim && i*nbim + j < (int)vVars.size(); j++) {
	  Glucose::vec<Glucose::Lit> pLits;
	  int RetValue;
	  pLits.push(Glucose::mkLit( vVars[i*nbim + j], 1 ));
	  pLits.push(Glucose::mkLit( c + k, 1 ));
	  std::cout << c + k << std::endl;
	  RetValue = pSat->addClause(pLits);  assert( RetValue );
	  nCount++;
	}
      }
    }
  }
}
int Bmc_MeshAddOneHotness2( Glucose::SimpSolver * pSat, int iFirst, int iLast )
{
    int i, j, v, nVars, nCount = 0;
    std::vector<int> pVars;
    assert( iFirst < iLast && iFirst + 110 > iLast );
    for ( v = iFirst; v < iLast; v++ )
        if ( Bmc_MeshVarValue2(pSat, v) ) // v = 1
            pVars.push_back(v);
    if ( pVars.size() <= 1 )
        return 0;
    
    nCount = bimander(pSat, pVars, 2);
    return nCount;
    
    // naive
    for ( i = 0;   i < pVars.size(); i++ )
    for ( j = i+1; j < pVars.size(); j++ )
    {
        Glucose::vec<Glucose::Lit> pLits;
	int RetValue;
        pLits.push(Glucose::mkLit( pVars[i], 1 ));
        pLits.push(Glucose::mkLit( pVars[j], 1 ));
        RetValue = pSat->addClause(pLits);  assert( RetValue );
        nCount++;
    }
    return nCount;
    /*
    // commander
    nVars = pVars.size();
    while ( nVars > 1 )
    {
	nVars = 0;
	for ( i = 0; i < pVars.size(); i += 2 )
	{
	    if( i == pVars.size() - 1 )
	    {
	      pVars[nVars++] = pVars[i];
	      break;
	    }
	    int c = pSat->newVar();
	    pSat->addClause(Glucose::mkLit( pVars[i], 1 ), Glucose::mkLit( pVars[i + 1], 1 ));
	    pSat->addClause(Glucose::mkLit( pVars[i], 1 ), Glucose::mkLit( c, 0 ));
	    pSat->addClause(Glucose::mkLit( pVars[i + 1], 1 ), Glucose::mkLit( c, 0 ));
	    pVars[nVars++] = c;
	    nCount += 3;
	}
	pVars.resize(nVars);
    }
    return nCount;
    */
    /*
    // binary
    nVars = integer_log2(pVars.size());
    for( j = 0; j < nVars; j++)
      {
	int c = pSat->newVar();
	int b = 1 << j;
	for ( i = 0; i < pVars.size(); i++ )
	  {
	    if(i & b)
		pSat->addClause(Glucose::mkLit( pVars[i], 1 ), Glucose::mkLit( c, 0 ));
	    else
		pSat->addClause(Glucose::mkLit( pVars[i], 1 ), Glucose::mkLit( c, 1 ));
	    nCount++;
	  }
      }
    return nCount;
    */
}

/**Function*************************************************************
  Synopsis    []
  Description []
               
  SideEffects []
  SeeAlso     []
***********************************************************************/
void Bmc_MeshTest( aigman * p, int X, int Y, int T, int fVerbose, bool inputbuf )
{
    Glucose::SimpSolver * pSat = new Glucose::SimpSolver;
    pSat->setIncrementalMode();
    pSat->use_elim = 0;
    std::vector<std::vector<int> > Me;
    std::vector<std::vector<int> > pN;
    int I = p->nPis;
    int G = I + p->nGates;
    int i, x, y, t, g, c, status, RetValue, Lit, iVar, nClauses = 0;

    assert(p->nPos == 1);

    Me.resize(X + 1);
    for ( x = 0; x < X; x++ )
        Me[x].resize(Y);
    Me[X].resize(2);

    pN.resize(G);
    for ( i = I; i < G; i++ )
        pN[i].resize(2);
    
    // init the graph
    for(int i = I + 1; i < G + 1; i++)
    {
	pN[i-1][0] = (p->vObjs[i + i] >> 1) - 1;
	pN[i-1][1] = (p->vObjs[i + i + 1] >> 1) - 1;
    }
    if ( fVerbose )
    {
        printf( "The graph has %d inputs: ", p->nPis );
        for ( i = 0; i < I; i++ )
            printf( "%c ", 'A' + i );
        printf( "  and %d nodes: ", p->nGates );
        for ( i = I; i < G; i++ )
            printf( "%c=%c%c ", 'A' + i, 'A' + pN[i][0] , 'A' + pN[i][1] );
        printf( "\n" );
    }

    // init SAT variables (time vars + graph vars + config vars)
    // config variables: 16 = 4 buff vars + 12 node vars
    iVar = 0;
    for ( y = 0; y < Y; y++ )
    for ( x = 0; x < X; x++ )
    {
        Me[x][y] = iVar;
        iVar += T + G + NCPARS + 1;
    }
    Me.back()[0] = T;
    Me.back()[1] = G;
    if ( fVerbose )
        printf( "SAT variable count is %d (%d time vars + %d graph vars + %d config vars + %d aux vars)\n", iVar, X*Y*T, X*Y*G, X*Y*NCPARS, X*Y );

    while(iVar >= pSat->nVars()) pSat->newVar();
    
    // add constraints

    // time 0 and primary inputs only on the boundary
    for ( x = 0; x < X; x++ )
    for ( y = 0; y < Y; y++ )
    {
        int iTVar = Bmc_MeshTVar( Me, x, y );
        int iGVar = Bmc_MeshGVar( Me, x, y );

        if ( x == 0 || x == X-1 || y == 0 || y == Y-1 ) // boundary
        {
            // time 0 is required
	    if ( !inputbuf )
            for ( t = 0; t < T; t++ )
            {
                RetValue = pSat->addClause( Glucose::mkLit( iTVar+t, (int)(t > 0) ) );  assert( RetValue );
            }
            // internal nodes are not allowed
            for ( g = I; g < G; g++ )
            {
                RetValue = pSat->addClause( Glucose::mkLit( iGVar+g, 1 ) );  assert( RetValue );
            }
        }
        else // not a boundary
        {
	    // cannot have time 0
            RetValue = pSat->addClause( Glucose::mkLit( iTVar, 1 ) );  assert( RetValue );
        }
    }
    for ( x = 1; x < X-1; x++ )
    for ( y = 1; y < Y-1; y++ )
    {
        Glucose::vec<Glucose::Lit> pLits;

        int iTVar = Bmc_MeshTVar( Me, x, y );
        int iGVar = Bmc_MeshGVar( Me, x, y );
        int iCVar = Bmc_MeshCVar( Me, x, y );
        int iUVar = Bmc_MeshUVar( Me, x, y );

        // 0=left  1=up  2=right  3=down
        int iTVars[4]; 
        int iGVars[4];

        iTVars[0] = Bmc_MeshTVar( Me, x-1, y );
        iGVars[0] = Bmc_MeshGVar( Me, x-1, y );

        iTVars[1] = Bmc_MeshTVar( Me, x, y-1 );
        iGVars[1] = Bmc_MeshGVar( Me, x, y-1 );

        iTVars[2] = Bmc_MeshTVar( Me, x+1, y );
        iGVars[2] = Bmc_MeshGVar( Me, x+1, y );

        iTVars[3] = Bmc_MeshTVar( Me, x, y+1 );
        iGVars[3] = Bmc_MeshGVar( Me, x, y+1 );

        // condition when cell is used
        for ( g = 0; g < G; g++ )
        {
	    pLits.clear();
            pLits.push(Glucose::mkLit( iGVar+g, 1 ));
            pLits.push(Glucose::mkLit( iUVar, 0 ));
            RetValue = pSat->addClause( pLits );  assert( RetValue );
            nClauses++;
        }

        // at least one time is used
	pLits.clear();
        pLits.push(Glucose::mkLit( iUVar, 1 ));
        for ( t = 1; t < T; t++ )
	    pLits.push(Glucose::mkLit( iTVar+t, 0 ));
        RetValue = pSat->addClause( pLits );  assert( RetValue );
        nClauses++;

        // at least one config is used
	pLits.clear();
        pLits.push(Glucose::mkLit( iUVar, 1 ));
        for ( c = 0; c < NCPARS; c++ )
	  pLits.push(Glucose::mkLit( iCVar+c, 0 ));
        RetValue = pSat->addClause( pLits );  assert( RetValue );
        nClauses++;

        // constraints for each time
        for ( t = 1; t < T; t++ )
        {
            int Conf[12][2] = {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},   {1, 0}, {2, 0}, {3, 0}, {2, 1}, {3, 1}, {3, 2}};
            // buffer
            for ( g = 0; g < G; g++ )
            for ( c = 0; c < 4; c++ )
            {
	        pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c, 1 ));
                pLits.push(Glucose::mkLit( iTVars[c]+t-1, 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

		pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c, 1 ));
                pLits.push(Glucose::mkLit( iGVars[c]+g, 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

                nClauses += 2;
            }
            for ( g = 0; g < I; g++ )
            for ( c = 4; c < NCPARS; c++ )
            {
	        pLits.clear();
	        pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c, 1 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );
                nClauses++;
            }
            // node
            for ( g = I; g < G; g++ )
            for ( c = 0; c < 12; c++ )
            {
                assert( pN[g][0] >= 0 && pN[g][1] >= 0 );
                assert( pN[g][0] <  g && pN[g][1] <  g );

                pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c+4, 1 ));
                pLits.push(Glucose::mkLit( iTVars[Conf[c][0]]+t-1, 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

		pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c+4, 1 ));
                pLits.push(Glucose::mkLit( iTVars[Conf[c][1]]+t-1, 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );


                pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c+4, 1 ));
                pLits.push(Glucose::mkLit( iGVars[Conf[c][0]]+pN[g][0], 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

		pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c+4, 1 ));
                pLits.push(Glucose::mkLit( iGVars[Conf[c][1]]+pN[g][1], 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

                nClauses += 4;
            }
        }
    }

    // final condition
    {
        int iGVar = Bmc_MeshGVar( Me, 1, 1 ) + G-1;
        RetValue = pSat->addClause( Glucose::mkLit( iGVar, 0 ) );
        if ( RetValue == 0 )
        {
            printf( "Problem has no solution. " );
            delete pSat;
            return;
        }
    }

    if ( fVerbose )
        printf( "Finished adding %d clauses. Started solving...\n", nClauses );

    while ( 1 )
    {
        int nAddClauses = 0;
	auto start = std::chrono::system_clock::now();
        status = pSat->solve();
	auto end = std::chrono::system_clock::now();
	std::cout << "time : " << std::chrono::duration_cast<std::chrono::milliseconds>(end-start).count() / 1000. << " s" << std::endl;
        if ( status == 0 )
        {
            printf( "Problem has no solution. " );
            break;
        }
        assert( status );
        // check if the solution is valid and add constraints
        for ( x = 0; x < X; x++ )
        for ( y = 0; y < Y; y++ )
        {
            if ( x == 0 || x == X-1 || y == 0 || y == Y-1 ) // boundary
            {
                int iGVar = Bmc_MeshGVar( Me, x, y );
                nAddClauses += Bmc_MeshAddOneHotness2( pSat, iGVar, iGVar + G );
		if ( inputbuf )
		{
		    int iTVar = Bmc_MeshTVar( Me, x, y );
		    nAddClauses += Bmc_MeshAddOneHotness2( pSat, iTVar, iTVar + T );
		}
            }
            else
            {
                int iTVar = Bmc_MeshTVar( Me, x, y );
                int iGVar = Bmc_MeshGVar( Me, x, y );
                int iCVar = Bmc_MeshCVar( Me, x, y );
                nAddClauses += Bmc_MeshAddOneHotness2( pSat, iTVar, iTVar + T );
                nAddClauses += Bmc_MeshAddOneHotness2( pSat, iGVar, iGVar + G );
                nAddClauses += Bmc_MeshAddOneHotness2( pSat, iCVar, iCVar + NCPARS );
            }
        }
        if ( nAddClauses > 0 )
        {
            printf( "Adding %d one-hotness clauses.\n", nAddClauses );
            continue;
        }
        printf( "Satisfying solution found. " );
        break;
    }
    if ( status )
    {
        // count the number of nodes and buffers
        int nBuffs = 0, nNodes = 0;
        for ( y = 1; y < Y-1; y++ )
        for ( x = 1; x < X-1; x++ )
        {
            int iCVar = Bmc_MeshCVar( Me, x, y );
            for ( c = 0; c < 4; c++ )
                if ( Bmc_MeshVarValue2(pSat, iCVar+c) )
                {
                    nBuffs++;
                }
            for ( c = 4; c < NCPARS; c++ )
                if ( Bmc_MeshVarValue2(pSat, iCVar+c) )
                {
                    nNodes++;
                }
        }
        printf( "The %d x %d mesh with latency %d with %d active cells (%d nodes and %d buffers):\n", X, Y, T, nNodes+nBuffs, nNodes, nBuffs );
        // print mesh
        printf( " Y\\X " );
        for ( x = 0; x < X; x++ )
            printf( "  %-2d ", x );
        printf( "\n" );
        for ( y = 0; y < Y; y++ )
        {
            printf( " %-2d  ", y );
            for ( x = 0; x < X; x++ )
            {
                int iTVar  = Bmc_MeshTVar( Me, x, y );
                int iGVar  = Bmc_MeshGVar( Me, x, y );

                int fFound = 0;                ;
                for ( t = 0; t < T; t++ )
                for ( g = 0; g < G; g++ )
                    if ( Bmc_MeshVarValue2(pSat, iTVar+t) && Bmc_MeshVarValue2(pSat, iGVar+g) )
                    {
                        printf( " %c%-2d ", 'A' + g, t );
                        fFound = 1;
                    }
                if ( fFound )
                    continue;
                if ( x == 0 || x == X-1 || y == 0 || y == Y-1 ) // boundary
                    printf( "  *  " );
                else
                    printf( "     " );
            }
            printf( "\n" );
        }
    }
    delete pSat;
}

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Bmc_MeshTest2( aigman * p, int X, int Y, int T, int fVerbose )
{
    Glucose::SimpSolver * pSat = new Glucose::SimpSolver;
    pSat->setIncrementalMode();
    pSat->use_elim = 0;
    std::vector<std::vector<int> > Me;
    std::vector<std::vector<int> > pN;
    int I = p->nPis;
    int G = I + p->nGates;
    int i, x, y, t, g, c, status, RetValue, Lit, iVar, nClauses = 0;

    Me.resize(X + 1);
    for ( x = 0; x < X; x++ )
        Me[x].resize(Y);
    Me[X].resize(2);

    pN.resize(G + 1);
    for ( i = I; i < G; i++ )
        pN[i].resize(2);
    
    // init the graph
    for ( i = I + 1; i < G + 1; i++ )
    {
	pN[i-1][0] = (p->vObjs[i + i] >> 1) - 1;
	pN[i-1][1] = (p->vObjs[i + i + 1] >> 1) - 1;
    }
    for ( i = 0; i < p->nPos; i++ )
        pN[G].push_back((p->vPos[i] >> 1) - 1);
    if ( fVerbose )
    {
        printf( "The graph has %d inputs: ", p->nPis );
        for ( i = 0; i < I; i++ )
            printf( "%c ", 'A' + i );
        printf( "  and %d nodes: ", p->nGates );
        for ( i = I; i < G; i++ )
            printf( "%c=%c%c ", 'A' + i, 'A' + pN[i][0] , 'A' + pN[i][1] );
        printf( "\n" );
    }

    // init SAT variables (time vars + graph vars + config vars)
    // config variables: 16 = 4 buff vars + 12 node vars
    iVar = 0;
    for ( y = 0; y < Y; y++ )
    for ( x = 0; x < X; x++ )
    {
        Me[x][y] = iVar;
        iVar += T + G + NCPARS + 1;
    }
    Me.back()[0] = T;
    Me.back()[1] = G;
    if ( fVerbose )
        printf( "SAT variable count is %d (%d time vars + %d graph vars + %d config vars + %d aux vars)\n", iVar, X*Y*T, X*Y*G, X*Y*NCPARS, X*Y );

    while(iVar >= pSat->nVars()) pSat->newVar();
    
    // add constraints

    // time 0 and primary inputs only on the boundary
    for ( x = 0; x < X; x++ )
    for ( y = 0; y < Y; y++ )
    {
        Glucose::vec<Glucose::Lit> pLits;
	      
        int iTVar = Bmc_MeshTVar( Me, x, y );
        int iGVar = Bmc_MeshGVar( Me, x, y );

        if ( x == 0 || x == X-1 || y == 0 || y == Y-1 ) // boundary
        {
	    /*
            // time 0 is required
            for ( t = 0; t < T; t++ )
            {
                RetValue = pSat->addClause( Glucose::mkLit( iTVar+t, (int)(t > 0) ) );  assert( RetValue );
            }
	    */
            // internal nodes are not allowed
            for ( g = I; g < G; g++ )
            {
	        pLits.clear();
	        pLits.push(Glucose::mkLit( iGVar+g, 1 ));
		if ( std::find(pN[G].begin(), pN[G].end(), g) != pN[G].end() )
		{
		    pLits.push(Glucose::mkLit( iTVar, 1 ));
		    nClauses++;
		}
		RetValue = pSat->addClause( pLits );  assert( RetValue );
            }
        }
        else // not a boundary
        {
	    // cannot have time 0
            RetValue = pSat->addClause( Glucose::mkLit( iTVar, 1 ) );  assert( RetValue );
        }
    }
    for ( x = 1; x < X-1; x++ )
    for ( y = 1; y < Y-1; y++ )
    {
        Glucose::vec<Glucose::Lit> pLits;

        int iTVar = Bmc_MeshTVar( Me, x, y );
        int iGVar = Bmc_MeshGVar( Me, x, y );
        int iCVar = Bmc_MeshCVar( Me, x, y );
        int iUVar = Bmc_MeshUVar( Me, x, y );

        // 0=left  1=up  2=right  3=down
        int iTVars[4]; 
        int iGVars[4];

        iTVars[0] = Bmc_MeshTVar( Me, x-1, y );
        iGVars[0] = Bmc_MeshGVar( Me, x-1, y );

        iTVars[1] = Bmc_MeshTVar( Me, x, y-1 );
        iGVars[1] = Bmc_MeshGVar( Me, x, y-1 );

        iTVars[2] = Bmc_MeshTVar( Me, x+1, y );
        iGVars[2] = Bmc_MeshGVar( Me, x+1, y );

        iTVars[3] = Bmc_MeshTVar( Me, x, y+1 );
        iGVars[3] = Bmc_MeshGVar( Me, x, y+1 );

        // condition when cell is used
        for ( g = 0; g < G; g++ )
        {
	    pLits.clear();
            pLits.push(Glucose::mkLit( iGVar+g, 1 ));
            pLits.push(Glucose::mkLit( iUVar, 0 ));
            RetValue = pSat->addClause( pLits );  assert( RetValue );
            nClauses++;
        }

        // at least one time is used
	pLits.clear();
        pLits.push(Glucose::mkLit( iUVar, 1 ));
        for ( t = 1; t < T; t++ )
	    pLits.push(Glucose::mkLit( iTVar+t, 0 ));
        RetValue = pSat->addClause( pLits );  assert( RetValue );
        nClauses++;

        // at least one config is used
	pLits.clear();
        pLits.push(Glucose::mkLit( iUVar, 1 ));
        for ( c = 0; c < NCPARS; c++ )
	  pLits.push(Glucose::mkLit( iCVar+c, 0 ));
        RetValue = pSat->addClause( pLits );  assert( RetValue );
        nClauses++;

        // constraints for each time
        for ( t = 1; t < T; t++ )
        {
            int Conf[12][2] = {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},   {1, 0}, {2, 0}, {3, 0}, {2, 1}, {3, 1}, {3, 2}};
            // buffer
            for ( g = 0; g < G; g++ )
            for ( c = 0; c < 4; c++ )
            {
	        pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c, 1 ));
                pLits.push(Glucose::mkLit( iTVars[c]+t-1, 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

		pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c, 1 ));
                pLits.push(Glucose::mkLit( iGVars[c]+g, 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

                nClauses += 2;
            }
            for ( g = 0; g < I; g++ )
            for ( c = 4; c < NCPARS; c++ )
            {
	        pLits.clear();
	        pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c, 1 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );
                nClauses++;
            }
            // node
            for ( g = I; g < G; g++ )
            for ( c = 0; c < 12; c++ )
            {
                assert( pN[g][0] >= 0 && pN[g][1] >= 0 );
                assert( pN[g][0] <  g && pN[g][1] <  g );

                pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c+4, 1 ));
                pLits.push(Glucose::mkLit( iTVars[Conf[c][0]]+t-1, 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

		pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c+4, 1 ));
                pLits.push(Glucose::mkLit( iTVars[Conf[c][1]]+t-1, 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );


                pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c+4, 1 ));
                pLits.push(Glucose::mkLit( iGVars[Conf[c][0]]+pN[g][0], 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

		pLits.clear();
                pLits.push(Glucose::mkLit( iTVar+t, 1 ));
                pLits.push(Glucose::mkLit( iGVar+g, 1 ));
                pLits.push(Glucose::mkLit( iCVar+c+4, 1 ));
                pLits.push(Glucose::mkLit( iGVars[Conf[c][1]]+pN[g][1], 0 ));
                RetValue = pSat->addClause( pLits );  assert( RetValue );

                nClauses += 4;
            }
        }
    }


    for ( x = 0; x < X; x++ )
    for ( y = 0; y < Y; y++ )
    if ( x == 0 || x == X-1 || y == 0 || y == Y-1 ) // boundary
    {
        Glucose::vec<Glucose::Lit> pLits;

        int iTVar = Bmc_MeshTVar( Me, x, y );
        int iGVar = Bmc_MeshGVar( Me, x, y );
        int iCVar = Bmc_MeshCVar( Me, x, y );
        int iUVar = Bmc_MeshUVar( Me, x, y );

        // 0=left  1=up  2=right  3=down
        int iTVars; 
        int iGVars;

	if ( x == X - 1 )
	{
	    iTVars = Bmc_MeshTVar( Me, x-1, y );
	    iGVars = Bmc_MeshGVar( Me, x-1, y );
	}

	if ( y == Y - 1 )
	{
	    iTVars = Bmc_MeshTVar( Me, x, y-1 );
	    iGVars = Bmc_MeshGVar( Me, x, y-1 );
	}

	if ( x == 0 )
	{
	    iTVars = Bmc_MeshTVar( Me, x+1, y );
	    iGVars = Bmc_MeshGVar( Me, x+1, y );
	}

	if ( y == 0 )
	{
	    iTVars = Bmc_MeshTVar( Me, x, y+1 );
	    iGVars = Bmc_MeshGVar( Me, x, y+1 );
	}

        // condition when cell is used
        for ( g = 0; g < I; g++ )
        {
	    pLits.clear();
            pLits.push(Glucose::mkLit( iGVar+g, 1 ));
            pLits.push(Glucose::mkLit( iUVar, 0 ));
            RetValue = pSat->addClause( pLits );  assert( RetValue );
            nClauses++;
        }
	for ( int g : pN[G] )
        {
	    pLits.clear();
            pLits.push(Glucose::mkLit( iGVar+g, 1 ));
            pLits.push(Glucose::mkLit( iUVar, 0 ));
            RetValue = pSat->addClause( pLits );  assert( RetValue );
            nClauses++;
        }

        // at least one time is used
	pLits.clear();
        pLits.push(Glucose::mkLit( iUVar, 1 ));
        for ( t = 0; t < T; t++ )
	    pLits.push(Glucose::mkLit( iTVar+t, 0 ));
        RetValue = pSat->addClause( pLits );  assert( RetValue );
        nClauses++;

        // constraints for each time
	// buffer
	for ( int g : pN[G] )
	for ( t = 1; t < T; t++ )
	{
	    pLits.clear();
	    pLits.push(Glucose::mkLit( iTVar+t, 1 ));
	    pLits.push(Glucose::mkLit( iGVar+g, 1 ));
	    pLits.push(Glucose::mkLit( iTVars+t-1, 0 ));
	    RetValue = pSat->addClause( pLits );  assert( RetValue );
	    
	    pLits.clear();
	    pLits.push(Glucose::mkLit( iTVar+t, 1 ));
	    pLits.push(Glucose::mkLit( iGVar+g, 1 ));
	    pLits.push(Glucose::mkLit( iGVars+g, 0 ));
	    RetValue = pSat->addClause( pLits );  assert( RetValue );
	    
	    nClauses += 2;
        }
    }


    // final condition
    {
        Glucose::vec<Glucose::Lit> pLits;
        for ( i = 0; i < p->nPos; i++ )
	{
	    pLits.clear();
	    for ( x = 0; x < X; x++ )
	    for ( y = 0; y < Y; y++ )
	    if ( x == 0 || x == X-1 || y == 0 || y == Y-1 ) // boundary
	    {
		int iGVar = Bmc_MeshGVar( Me, x, y ) + (p->vPos[i] >> 1) - 1;
		pLits.push( Glucose::mkLit( iGVar, 0 ) );
	    }
	    RetValue = pSat->addClause( pLits );
	    if ( RetValue == 0 )
	    {
		printf( "Problem has no solution. " );
		delete pSat;
		return;
	    }
	    nClauses++;
	}
    }
    if ( fVerbose )
        printf( "Finished adding %d clauses. Started solving...\n", nClauses );

    while ( 1 )
    {
        int nAddClauses = 0;
	auto start = std::chrono::system_clock::now();
        status = pSat->solve();
	auto end = std::chrono::system_clock::now();
	std::cout << "time : " << std::chrono::duration_cast<std::chrono::milliseconds>(end-start).count() / 1000. << " s" << std::endl;
        if ( status == 0 )
        {
            printf( "Problem has no solution. " );
            break;
        }
        assert( status );
        // check if the solution is valid and add constraints
        for ( x = 0; x < X; x++ )
        for ( y = 0; y < Y; y++ )
        {
	    if ( x == 0 || x == X-1 || y == 0 || y == Y-1 ) // boundary
	    {
		int iTVar = Bmc_MeshTVar( Me, x, y );
		int iGVar = Bmc_MeshGVar( Me, x, y );
		nAddClauses += Bmc_MeshAddOneHotness2( pSat, iTVar, iTVar + T );
		nAddClauses += Bmc_MeshAddOneHotness2( pSat, iGVar, iGVar + G );
	    }
	    else
	    {
		int iTVar = Bmc_MeshTVar( Me, x, y );
		int iGVar = Bmc_MeshGVar( Me, x, y );
		int iCVar = Bmc_MeshCVar( Me, x, y );
		nAddClauses += Bmc_MeshAddOneHotness2( pSat, iTVar, iTVar + T );
		nAddClauses += Bmc_MeshAddOneHotness2( pSat, iGVar, iGVar + G );
		nAddClauses += Bmc_MeshAddOneHotness2( pSat, iCVar, iCVar + NCPARS );
	    }
        }
        if ( nAddClauses > 0 )
        {
            printf( "Adding %d one-hotness clauses.\n", nAddClauses );
            continue;
        }
        printf( "Satisfying solution found. " );
        break;
    }
    if ( status )
    {
        // count the number of nodes and buffers
        int nBuffs = 0, nNodes = 0;
        for ( y = 1; y < Y-1; y++ )
        for ( x = 1; x < X-1; x++ )
        {
            int iCVar = Bmc_MeshCVar( Me, x, y );
            for ( c = 0; c < 4; c++ )
                if ( Bmc_MeshVarValue2(pSat, iCVar+c) )
                {
                    nBuffs++;
                }
            for ( c = 4; c < NCPARS; c++ )
                if ( Bmc_MeshVarValue2(pSat, iCVar+c) )
                {
                    nNodes++;
                }
        }
        printf( "The %d x %d mesh with latency %d with %d active cells (%d nodes and %d buffers):\n", X, Y, T, nNodes+nBuffs, nNodes, nBuffs );
        // print mesh
        printf( " Y\\X " );
        for ( x = 0; x < X; x++ )
            printf( "  %-2d ", x );
        printf( "\n" );
        for ( y = 0; y < Y; y++ )
        {
            printf( " %-2d  ", y );
            for ( x = 0; x < X; x++ )
            {
                int iTVar  = Bmc_MeshTVar( Me, x, y );
                int iGVar  = Bmc_MeshGVar( Me, x, y );

                int fFound = 0;                ;
                for ( t = 0; t < T; t++ )
                for ( g = 0; g < G; g++ )
                    if ( Bmc_MeshVarValue2(pSat, iTVar+t) && Bmc_MeshVarValue2(pSat, iGVar+g) )
                    {
                        printf( " %c%-2d ", 'A' + g, t );
                        fFound = 1;
                    }
                if ( fFound )
                    continue;
                if ( x == 0 || x == X-1 || y == 0 || y == Y-1 ) // boundary
                    printf( "  *  " );
                else
                    printf( "     " );
            }
            printf( "\n" );
        }
    }
    delete pSat;
}




////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
