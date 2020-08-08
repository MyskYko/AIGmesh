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
int Bmc_MeshAddOneHotness2( Glucose::SimpSolver * pSat, int iFirst, int iLast )
{
    int i, j, v, pVars[100], nVars  = 0, nCount = 0;
    assert( iFirst < iLast && iFirst + 110 > iLast );
    for ( v = iFirst; v < iLast; v++ )
        if ( Bmc_MeshVarValue2(pSat, v) ) // v = 1
        {
            assert( nVars < 100 );
            pVars[ nVars++ ] = v;
        }
    if ( nVars <= 1 )
        return 0;
    for ( i = 0;   i < nVars; i++ )
    for ( j = i+1; j < nVars; j++ )
    {
        Glucose::vec<Glucose::Lit> pLits;
	int RetValue;
        pLits.push(Glucose::mkLit( pVars[i], 1 ));
        pLits.push(Glucose::mkLit( pVars[j], 1 ));
        RetValue = pSat->addClause(pLits);  assert( RetValue );
        nCount++;
    }
    return nCount;
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
    for ( i = 0; i < G + 1; i++ )
        pN[i].resize(2);
    
    // init the graph
    for ( i = 0; i < I; i++ )
        pN[i][0] = pN[i][1] = -1;
    for(int i = I + 1; i < G + 1; i++)
    {
	pN[i-1][0] = (p->vObjs[i + i] >> 1) - 1;
	pN[i-1][1] = (p->vObjs[i + i + 1] >> 1) - 1;
    }
    if ( fVerbose )
    {
        printf( "The graph has %d inputs: ", p->nPis );
        for ( i = 0; i < I; i++ )
            printf( "%c ", 'a' + i );
        printf( "  and %d nodes: ", p->nGates );
        for ( i = I; i < G; i++ )
            printf( "%c=%c%c ", 'a' + i, 'a' + pN[i][0] , 'a' + pN[i][1] );
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
        status = pSat->solve();
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
                        printf( " %c%-2d ", 'a' + g, t );
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
