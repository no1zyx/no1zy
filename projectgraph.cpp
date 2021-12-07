#include <iostream>
#include <vector>
#include <queue>
#include <stack>
#include <string>
#include <conio.h>
#include <time.h>
#include <algorithm>

using namespace std;

template <class keyType> class PQi
{
	int d, N;
	vector<int> pq, qp;
	const vector<keyType>& a;
	void exch(int i, int j)
	{
		int t = pq[i]; pq[i] = pq[j]; pq[j] = t;
		qp[pq[i]] = i; qp[pq[j]] = j;
	}
	void fixUp(int k)
	{
		while (k > 1 && a[pq[(k + d - 2) / d]] > a[pq[k]])
		{
			exch(k, (k + d - 2) / d); k = (k + d - 2) / d;
		}
	}
	void fixDown(int k, int N)
	{
		int j;
		while ((j = d * (k - 1) + 2) <= N)
		{
			for (int i = j + 1; i < j + d && i <= N; i++)
				if (a[pq[j]] > a[pq[i]]) j = i;
			if (!(a[pq[k]] > a[pq[j]])) break;
			exch(k, j); k = j;
		}
	}
public:
	PQi(int N, const vector<keyType>& a, int d = 3) :
		a(a), pq(N + 1, 0), qp(N + 1, 0), N(0), d(d) { }
	int empty() const { return N == 0; }
	void insert(int v)
	{
		pq[++N] = v; qp[v] = N; fixUp(N);
	}
	int getmin()
	{
		exch(1, N); fixDown(1, N - 1); return pq[N--];
	}
	void lower(int k)
	{
		fixUp(qp[k]);
	}
};

class EDGE
{
	int v_, w_;
	double wt_;
public:
	EDGE(int v__ = -1, int w__ = -1, double wt__ = 0.0) : v_(v__), w_(w__), wt_(wt__) {}
	int v() const { return v_; }
	int w() const { return w_; }
	double wt() const { return wt_; }
	bool from(int v_) const { return v_ == this->v_; }
	int other(int) const {}
	void show(void) { cout << v() << " - " << w() << endl; }
};

template <class Edge>
class EdgePtr
{
public:
	Edge* item;
	EdgePtr(Edge* item = NULL) : item(item) {}
	bool operator<(const EdgePtr& e)
	{
		return item->wt() < e.item->wt();
	}
	Edge* operator->(void)
	{
		return item;
	}

	operator Edge* (void) const
	{
		return item;
	}
};

//---------------------------------------------------------------------

template <class Edge>
class GRAPH
{

public:
	virtual ~GRAPH(void) {}
	virtual int V() const = 0;
	virtual int E() const = 0;
	virtual bool directed() const = 0;
	virtual void insert(Edge* e) = 0;
	virtual void remove(Edge* e) = 0;
	virtual void removeV(int w) = 0;
	virtual Edge* edge(int v, int w) const = 0;
	virtual void print(void) = 0;

	class adjIterator;
	friend class adjIterator;
};

//---------------------------------------------------------------------

template <class Edge>
class DenseGRAPH : public GRAPH<Edge>
{
	int Vcnt, Ecnt; bool digraph;
	vector <vector <Edge*> > adj;
public:
	DenseGRAPH(int V, bool digraph = false) :
		adj(V), Vcnt(V), Ecnt(0), digraph(digraph)
	{
		for (int i = 0; i < V; i++)
			adj[i].assign(V, 0);
	}
	~DenseGRAPH(void)
	{
		for (int i = 0; i < V(); i++)
			for (int j = 0; j < V(); j++)
				if (adj[i][j])
					delete adj[i][j];
	}
	int V() const { return Vcnt; }
	int E() const { return Ecnt; }
	bool directed() const { return digraph; }
	void insert(Edge* e)
	{
		int v = e->v(), w = e->w();
		if (adj[v][w] == 0)
			Ecnt++;
		adj[v][w] = e;
		if (!digraph)
			adj[w][v] = new Edge(w, v, e->wt());
	}

	void remove(Edge* e)
	{
		int v = e->v(), w = e->w();
		if (adj[v][w] != 0)
			Ecnt--;
		adj[v][w] = 0;
		if (!digraph)
			adj[w][v] = 0;
	}
	void removeV(int w)
	{
		for (int i = 0; i < V(); i++)
			if (edge(i, w))
				remove(edge(i, w));
	}
	Edge* edge(int v, int w) const
	{
		return adj[v][w];
	}
	void print(void)
	{
		for (int i = 0; i < V(); cout << endl, i++)
			for (int j = 0; j < V(); j++)
				if (edge(i, j))
					cout << edge(i, j)->wt() << "\t";
				else
					cout << "-" << "\t";
	}

	class adjIterator;
	friend class adjIterator;
};

//------------------------------------------------------------------------

template <class Edge>
class DenseGRAPH<Edge>::adjIterator
{
	const DenseGRAPH<Edge>& G;
	int i, v;
public:
	adjIterator(const DenseGRAPH<Edge>& G, int v) :
		G(G), v(v), i(0) {}
	Edge* beg()
	{
		i = -1; return nxt();
	}
	Edge* nxt()
	{
		for (i++; i < G.V(); i++)
			if (G.edge(v, i))
				return G.adj[v][i];
		return 0;
	}
	bool end() const
	{
		return i >= G.V();
	}
};

//------------------------------------------------------------------------

template <class Edge>
class SparseMultiGRAPH : public GRAPH<Edge>
{
	int Vcnt, Ecnt;
	bool digraph;

	struct node
	{
		Edge* e;
		node* next;
		node(Edge* e, node* t)
		{
			this->e = e;
			next = t;
		}
	};

	typedef node* link;
	vector <link> adj;

public:
	SparseMultiGRAPH(int V, bool digraph = false) :
		adj(V), Vcnt(V), Ecnt(0), digraph(digraph)
	{
		adj.assign(V, 0);
	}
	int V() const { return Vcnt; }
	int E() const { return Ecnt; }
	bool directed() const { return digraph; }
	void insert(Edge* e)
	{
		int v = e->v(), w = e->w();
		adj[v] = new node(e, adj[v]);
		if (!digraph)
			adj[w] = new node(new Edge(w, v, e->wt()), adj[w]);
		Ecnt++;
	}
	void remove(Edge* e)
	{
		if (!e)
			return;

		int v = e->v(), w = e->w();
		link prev = adj[v];
		if (!prev)
			return;
		if (prev->e->w() == w)
		{
			adj[v] = prev->next;
			Ecnt--;
			return;
		}
		for (link next = prev->next; next; prev = prev->next, next = next->next)
			if (next->e->w() == w)
			{
				prev->next = next->next;
				Ecnt--;
				return;
			}
	}
	void removeV(int w)
	{
		for (link iter = adj[w]; iter;)
		{
			link del = iter;
			iter = iter->next;
		}
		adj[w] = NULL;

		for (int i = 0; i < V(); i++)
			remove(edge(i, w));
	}
	Edge* edge(int v, int w) const
	{
		link iter = adj[v];
		if (!iter)
			return NULL;

		while (iter)
			if (iter->e->w() == w)
				return iter->e;
			else
				iter = iter->next;

		return NULL;
	}
	void print(void)
	{
		for (int i = 0; i < V(); i++)
		{
			cout << i << " - ";
			for (link iter = adj[i]; iter; iter = iter->next)
				cout << iter->e->w() << ": " << iter->e->wt() << "\t";
			cout << endl;
		}
	}

	class adjIterator;
	friend class adjIterator;
};

//-------------------------------------------------------------------------

template <class Edge>
class SparseMultiGRAPH<Edge>::adjIterator
{
	const SparseMultiGRAPH<Edge>& G;
	int v;
	link t;
public:
	adjIterator(const SparseMultiGRAPH<Edge>& G, int v) :
		G(G), v(v)
	{
		t = 0;
	}
	Edge* beg()
	{
		t = G.adj[v];
		if (t)
			return t->e;
		else
			return NULL;
	}
	Edge* nxt()
	{
		if (t)
		{
			t = t->next;
			if (t)
				return t->e;
			return NULL;
		}
		return NULL;
	}
	bool end()
	{
		return t == 0;
	}
};

//-------------------------------------------------------------------------------

template <class Graph> class Connectivity
{
private:
	const Graph& G;
	bool checkCollumn(int k)
	{
		for (int i = 0; i < G.V(); i++)
			if (G.edge(i, k))
				return true;
		return false;
	}

public:
	Connectivity(const Graph& G) : G(G) {}

	bool check(void)
	{
		for (int i = 0; i < G.V(); i++)
		{
			typename Graph::adjIterator A(G, i);
			if (!A.beg())
				if (!checkCollumn(i))
					return false;
		}
		return true;
	}
};

//---------------------------------------------------------------------------------

template <class Graph, class Edge>
class SPT_Deikstra
{
	const Graph& G;
	vector< double > wt;
	vector< Edge* > spt;
	int istok;
public:
	SPT_Deikstra(const Graph& G, int s) : G(G), spt(G.V()), wt(G.V(), G.V()), istok(s)
	{
		for (int i = 0; i < G.V(); i++)
			spt[i] = NULL;

		PQi<double> pQ(G.V(), wt);
		for (int v = 0; v < G.V(); v++)
			pQ.insert(v); //заповнення дуже великими числами
		wt[s] = 0.0; pQ.lower(s);
		while (!pQ.empty())
		{
			int v = pQ.getmin(); // wt[v] = 0.0;
			if (v != s && spt[v] == 0)
				return;
			typename Graph::adjIterator A(G, v);
			for (Edge* e = A.beg(); !A.end(); e = A.nxt())
			{
				int w = e->w();
				double P = wt[v] + e->wt();
				if (P < wt[w])
				{
					wt[w] = P;
					pQ.lower(w);
					spt[w] = e;
				}
			}
		}
	}
	void print(int stok = -1)
	{
		if (stok >= 0)
		{
			if (!pathR(stok))
			{
				cout << "Кратчайшего пути от истока до стоковой вершины не существует" << endl;
				return;
			}

			cout << "\nДлина пути от истока до стока: " << wt[stok] << endl;

			cout << "Кратчайший маршрут от истока до стоковой вершины: ";
			cout << istok << " ";
			for (int j = stok;;)
			{
				if (pathR(j))
				{
					cout << pathR(j)->w() << " ";
					if (pathR(j)->w() == stok)
					{
						cout << endl;
						return;
					}
					j = pathR(j)->w();
				}
				else
					return;
			}
			return;
		}

		cout << "\n\nКратчайшие пути от истока ко всем парам вершин";
		cout << "\nВектор кратчайших путей: ";
		for (int j = 0; j < G.V(); j++)
			if (j == istok || !pathR(j))
				cout << "- ";
			else
				cout << pathR(j)->v() << " ";

		cout << "\nВектор кратчайших весов: ";
		for (int i = 0; i < G.V(); i++)
			if (pathR(i))
				cout << wt[i] << " ";
			else
				cout << "- ";
		cout << endl;
	}

	Edge* pathR(int v) const { return spt[v]; }
	double dist(int v) const { return wt[v]; }
};

//-------------------------------------------------------------------------------------

template <class Graph, class Edge>
class allSP_Deikstra //Метод Дейкстри для всіх пар вершин
{
	const Graph& G;
	vector< SPT_Deikstra<Graph, Edge>*> A;
public:
	allSP_Deikstra(const Graph& G) : G(G), A(G.V())
	{
		for (int s = 0; s < G.V(); s++)
			A[s] = new SPT_Deikstra<Graph, Edge>(G, s);
	}

	Edge* pathR(int s, int t) const
	{
		return A[s]->pathR(t);
	}

	double dist(int s, int t) const
	{
		return A[s]->dist(t);
	}

	void print(void)
	{
		int N = G.V();
		cout << "Матрица путей: " << endl;
		for (int i = 0; i < N; i++)
		{
			for (int j = 0; j < N; j++)
			{
				if (i == j)
					cout << "-";
				else if (pathR(j, i))
					cout << pathR(j, i)->v();
				cout << "\t";
			}
			cout << endl;
		}
		cout << endl;

		//--------------------------------------------------------------------------------

		cout << "Матрица весов: " << endl;
		for (int i = 0; i < N; i++)
		{
			for (int j = 0; j < N; j++)
			{
				if (i == j)
					cout << "-";
				else if (pathR(j, i))
					cout << dist(j, i);
				cout << "\t";
			}
			cout << endl;
		}
		cout << endl;
	}
};

//-------------------------------------------------------------------------------

template <class Graph> class SEARCH
{
protected:
	const Graph& G;
	int cnt;
	vector <int> ord;
	vector <int> obhod;
	virtual void searchC(EDGE) = 0;
	virtual void search()
	{
		for (int v = 0; v < G.V(); v++)
			if (ord[v] == -1)
				searchC(EDGE(v, v));
	}
public:
	SEARCH(const Graph& G) : G(G), ord(G.V(), -1), cnt(0) {}
	int operator[](int v) const { return ord[v]; }
	void print(void)
	{
		for (int i = 0; i < G.V(); i++)
			cout << this->obhod[i] << " "; cout << endl;
	}
};

//---------------------------------------------------------------------------------------

template <class Graph>
class DFS_ : public SEARCH<Graph>
{
public:
	DFS_(const Graph& G) : SEARCH<Graph>(G) {}
	virtual int ST(int v) const { return -1; }
};

//---------------------------------------------------------------------------------------

template <class Graph>
class DFS : public DFS_<Graph>
{
	vector<int> st;
	void searchC(EDGE e)
	{
		int w = e.w();
		this->obhod.push_back(e.w());
		this->ord[w] = this->cnt++; st[e.w()] = e.v();
		typename Graph::adjIterator A(this->G, w);
		for (EDGE* t = A.beg(); !A.end(); t = A.nxt())
			if ((this->ord[t->w()] == -1) && (t->v() != t->w()))
				searchC(EDGE(w, t->w()));
	}
public:
	DFS(const Graph& G) : DFS_<Graph>(G), st(G.V(), -1)
	{
		this->search();
	}
	int ST(int v) const { return st[v]; }
};

//---------------------------------------------------------------------------------------

template <class Graph>
class TOP_Sort : public SEARCH<Graph>
{
	Graph NewG;
	vector<int> st;
	void searchC(EDGE e)
	{
		int w = e.w();
		this->ord[w] = this->cnt++;
		typename Graph::adjIterator A(NewG, w);
		EDGE* t = A.beg();
		for (; !A.end(); t = A.nxt())
			if ((this->ord[t->w()] == -1) && (t->v() != t->w()))
				searchC(EDGE(w, t->w()));

		st.push_back(w);
		NewG.removeV(w);
	}
public:
	TOP_Sort(const Graph& G) : SEARCH<Graph>(G), NewG(G)
	{
		this->search();
	}

	int ST(int v) const
	{
		if (v < st.size())
			return st[st.size() - v - 1];
		else
			return -1;
	}
	void print(void)
	{
		cout << "Результат топологической сортировки: " << endl;
		for (int i = 0; i < this->G.V(); i++)
			cout << ST(i) << " "; cout << endl;
	}
};

//---------------------------------------------------------------------------------------

class UF
{
private:
	int* id, * sz;
	int find(int x)
	{
		while (x != id[x])
			x = id[x];
		return x;
	}

public:
	UF(int N)
	{
		id = new int[N];
		sz = new int[N];
		for (int i = 0; i < N; i++)
		{
			id[i] = i;
			sz[i] = 1;
		}
	}

	int find(int p, int q)
	{
		return (find(p) == find(q));
	}

	void unite(int p, int q)
	{
		int i = find(p), j = find(q);
		if (i == j)
			return;
		if (sz[i] < sz[j])
		{
			id[i] = j;
			sz[j] += sz[i];
		}
		else
		{
			id[j] = i;
			sz[i] += sz[j];
		}
	}
};

template <class Graph, class Edge, class EdgePtr>
vector <EdgePtr> edges(Graph& G)
{
	int E = 0;
	vector <EdgePtr> a(G.E());
	for (int v = 0; v < G.V(); v++)
	{
		typename Graph::adjIterator A(G, v);
		for (Edge* e = A.beg(); !A.end(); e = A.nxt())
			if (e->from(v))
				a[E++] = EdgePtr(e);
	}
	return a;
}

template <class Graph, class Edge, class EdgePtr>
class MST_Kruskal
{
	const Graph& G;
	vector<EdgePtr> a, mst;
	UF uf;
public:
	MST_Kruskal(Graph& G) : G(G), uf(G.V()), mst(G.V())
	{
		int V = G.V(), E = G.E();
		a = edges<Graph, Edge, EdgePtr>(G);
		sort(a.begin(), a.end());
		for (int i = 0, k = 1; i < E && k < V; i++)
			if (!uf.find(a[i]->v(), a[i]->w()))
			{
				uf.unite(a[i]->v(), a[i]->w());
				mst[k++] = a[i];
			}
	}

	void show()
	{
		for (int v = 1; v < G.V(); v++)
			if (mst[v])
				mst[v]->show();
	}

	double weight(void)
	{
		double w = 0;
		for (int v = 1; v < G.V(); v++)
			if (mst[v])
				w += mst[v]->wt();
		return w;
	}
};

//-----------------------------------------------------------------------------

template <class Graph, class EdgePtr>
class HEADTree_ : public SEARCH<Graph>
{
protected:
	vector<int> st;
	vector<EdgePtr> mst;

public:
	HEADTree_(const Graph& G) : SEARCH<Graph>(G), st(G.V(), -1) {}

	int ST(int v) const
	{
		return st[v];
	}

	void show()
	{
		for (int v = 0; v < mst.size(); v++)
			if (mst[v])
				mst[v]->show();
	}

	double weight(void)
	{
		double w = 0;
		for (int v = 0; v < mst.size(); v++)
			if (mst[v])
				w += mst[v]->wt();
		return w;
	}
};

//-----------------------------------------------------------------------------

template <class Graph, class EdgePtr>
class HEADTree : public HEADTree_<Graph, EdgePtr>
{
	void searchC(EDGE e)
	{
		int w = e.w();
		this->st[e.w()] = e.v();
		typename Graph::adjIterator A(this->G, w);
		for (EDGE* t = A.beg(); !A.end(); t = A.nxt())
			if (t->v() != t->w())
				if ((this->ord[t->w()] == -1))
				{
					this->ord[t->v()] = this->cnt++;
					this->ord[t->w()] = this->cnt++;
					this->mst.push_back(EdgePtr(t));
					searchC(EDGE(w, t->w()));
				}
				else if (this->ord[t->v()] == -1)
				{
					this->ord[t->v()] = this->cnt++;
					this->mst.push_back(EdgePtr(t));
				}
	}
public:
	HEADTree(const Graph& G) : HEADTree_<Graph, EdgePtr>(G)
	{
		this->search();
	}
};

//---------------------------------------------------------------------------------------

class Interaction
{
	DenseGRAPH< EDGE >* D_G;
	SparseMultiGRAPH< EDGE >* S_M_G;
	int N, E;

	void block1(string objName)
	{
		GRAPH<EDGE>* G = NULL;
		if (objName == "DenseGraph")
			G = D_G;
		else if (objName == "SparseMultiGRAPH")
			G = S_M_G;

		if (objName == "DenseGraph")
		{
			Connectivity< DenseGRAPH<EDGE> > con(*D_G);
			if (con.check())
				cout << "Граф связный." << endl;
			else
				cout << "Граф не связный." << endl;

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(con) << endl;
		}
		else
		{
			Connectivity< SparseMultiGRAPH<EDGE> > con(*S_M_G);
			if (con.check())
				cout << "Граф связный." << endl;
			else
				cout << "Граф не связный." << endl;

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(con) << endl;
		}
	}

	void block2(string objName)
	{
		GRAPH<EDGE>* G = NULL;
		if (objName == "DenseGraph")
			G = D_G;
		else if (objName == "SparseMultiGRAPH")
			G = S_M_G;

		if (objName == "DenseGraph")
		{
			DFS_< DenseGRAPH<EDGE> >* dfs = new DFS< DenseGRAPH<EDGE> >(*D_G);

			dfs->print();

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(*dfs) << endl;

			delete dfs;
		}
		else
		{
			DFS_< SparseMultiGRAPH<EDGE> >* dfs = new DFS< SparseMultiGRAPH<EDGE> >(*S_M_G);

			for (int i = 0; i < N; i++)
				cout << (*dfs)[i] << " "; cout << endl;

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(*dfs) << endl;

			delete dfs;
		}
	}

	void block3(string objName, int istok, int stok)
	{
		GRAPH<EDGE>* G = NULL;
		if (objName == "DenseGraph")
			G = D_G;
		else if (objName == "SparseMultiGRAPH")
			G = S_M_G;

		if (objName == "DenseGraph")
		{
			SPT_Deikstra<DenseGRAPH< EDGE >, EDGE> sp_D(*D_G, istok);
			sp_D.print(stok);
			sp_D.print();

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(sp_D) << endl;

			allSP_Deikstra< DenseGRAPH< EDGE >, EDGE > allsp_D(*D_G);
			cout << "\nКратчайшие пути между всеми парами вершин" << endl;
			allsp_D.print();

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(allsp_D) << endl;
		}
		else
		{
			SPT_Deikstra<SparseMultiGRAPH< EDGE >, EDGE> sp_D(*S_M_G, istok);
			sp_D.print(stok);
			sp_D.print();

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(sp_D) << endl;

			allSP_Deikstra< SparseMultiGRAPH< EDGE >, EDGE > allsp_D(*S_M_G);
			cout << "\nКратчайшие пути между всеми парами вершин" << endl;
			allsp_D.print();

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(allsp_D) << endl;
		}
	}

	void block4(string objName)
	{
		GRAPH<EDGE>* G = NULL;
		if (objName == "DenseGraph")
			G = D_G;
		else if (objName == "SparseMultiGRAPH")
			G = S_M_G;

		if (objName == "DenseGraph")
		{
			TOP_Sort< DenseGRAPH<EDGE> > sort(*D_G);
			sort.print();

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(sort) << endl;
		}
		else
		{
			TOP_Sort< SparseMultiGRAPH<EDGE> > sort(*S_M_G);
			sort.print();

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(sort) << endl;
		}
	}

	void block5(string objName)
	{
		GRAPH<EDGE>* G = NULL;
		if (objName == "DenseGraph")
			G = D_G;
		else if (objName == "SparseMultiGRAPH")
			G = S_M_G;
		if (!G)
		{
			cout << "Граф не задан! Сгенерируйте сначала граф (меню - 0)." << endl;
			return;
		}

		if (objName == "DenseGraph")
		{
			HEADTree_<DenseGRAPH< EDGE >, EdgePtr< EDGE >>* st = new HEADTree<DenseGRAPH< EDGE >, EdgePtr< EDGE >>(*D_G);

			cout << "\nРебра остовного дерева:" << endl;
			st->show();
			cout << "Общий вес дерева:" << st->weight() << endl;

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(st) << endl;
		}
		else
		{
			HEADTree_<SparseMultiGRAPH< EDGE >, EdgePtr< EDGE >>* st = new HEADTree<SparseMultiGRAPH< EDGE >, EdgePtr< EDGE >>(*S_M_G);

			cout << "\nРебра остовного дерева:" << endl;
			st->show();
			cout << "Общий вес дерева:" << st->weight() << endl;

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(st) << endl;
		}
	}

	void block6(string objName)
	{
		GRAPH<EDGE>* G = NULL;
		if (objName == "DenseGraph")
			G = D_G;
		else if (objName == "SparseMultiGRAPH")
			G = S_M_G;

		if (objName == "DenseGraph")
		{
			MST_Kruskal<DenseGRAPH< EDGE >, EDGE, EdgePtr< EDGE >> mst(*D_G);
			cout << "\nРебра минимального остовного дерева:" << endl;
			mst.show();
			cout << "Общий вес дерева:" << mst.weight() << endl;

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(mst) << endl;
		}
		else
		{
			MST_Kruskal<SparseMultiGRAPH< EDGE >, EDGE, EdgePtr< EDGE >> mst(*S_M_G);
			cout << "\nРебра минимального остовного дерева:" << endl;
			mst.show();
			cout << "Общий вес дерева:" << mst.weight() << endl;

			cout << "\nКоличество затрачиваемой памяти: " << sizeof(mst) << endl;
		}
	}

	void print(string objName)
	{
		GRAPH<EDGE>* G = NULL;
		if (objName == "DenseGraph")
			G = D_G;
		else if (objName == "SparseMultiGRAPH")
			G = S_M_G;

		if (objName == "DenseGraph")
			D_G->print();
		else
			S_M_G->print();
	}

public:
	Interaction(void) : D_G(NULL), S_M_G(NULL), N(0)
	{
		run();
	}

	~Interaction(void)
	{
		if (D_G)
			delete D_G;
		if (S_M_G)
			delete S_M_G;
	}

private:
	void run(void)
	{
		setlocale(0, "rus");

		cout << "\n//////////////////////////////////////////////////////////////\n";

		cout << "\nГраф на основе матрицы смежности.\n\n";
		N = 5;
		D_G = new DenseGRAPH< EDGE >(N, 1);
		D_G->insert(new EDGE(0, 4, 0.7));
		D_G->insert(new EDGE(1, 2, 0.8));
		D_G->insert(new EDGE(2, 3, 0.55));
		D_G->insert(new EDGE(0, 3, 0.8));
		D_G->insert(new EDGE(4, 3, 0.7));

		cout << "Наш граф:" << endl;
		print("DenseGraph");
		cout << "\nКоличество затрачиваемой памяти: " << sizeof(D_G) << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nПроверка графа на связность:" << endl;
		int t1 = clock();
		block1("DenseGraph");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nОбход графа в глубину:" << endl;
		t1 = clock();
		block2("DenseGraph");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nТопологическая сортировка:" << endl;
		t1 = clock();
		block4("DenseGraph");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		D_G->insert(new EDGE(4, 0, 0.7));
		D_G->insert(new EDGE(2, 1, 0.8));
		D_G->insert(new EDGE(3, 2, 0.55));
		D_G->insert(new EDGE(3, 0, 0.8));
		D_G->insert(new EDGE(3, 4, 0.7));
		cout << "\nМетод Дейкстры (для неориентированного графа)" << endl;
		cout << "\nИсток - 0, сток - 3" << endl;
		t1 = clock();
		block3("DenseGraph", 0, 3);
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nПостроение остовного дерева:" << endl;
		t1 = clock();
		block5("DenseGraph");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nПостроение минимального остовного дерева методом Краскала:" << endl;
		t1 = clock();
		block6("DenseGraph");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n//////////////////////////////////////////////////////////////\n";

		cout << "\nГраф на основе списков смежности.\n\n";
		N = 5;
		S_M_G = new SparseMultiGRAPH< EDGE >(N, 1);
		S_M_G->insert(new EDGE(0, 4, 0.7));
		S_M_G->insert(new EDGE(1, 2, 0.8));
		S_M_G->insert(new EDGE(2, 3, 0.55));
		S_M_G->insert(new EDGE(0, 3, 0.8));
		S_M_G->insert(new EDGE(4, 3, 0.7));

		cout << "Наш граф:" << endl;
		print("SparseMultiGRAPH");

		cout << "\nКоличество затрачиваемой памяти: " << sizeof(S_M_G) << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nПроверка графа на связность:" << endl;
		t1 = clock();
		block1("SparseMultiGRAPH");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nОбход графа в глубину:" << endl;
		t1 = clock();
		block2("SparseMultiGRAPH");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nТопологическая сортировка:" << endl;
		t1 = clock();
		block4("SparseMultiGRAPH");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		S_M_G->insert(new EDGE(4, 0, 0.7));
		S_M_G->insert(new EDGE(2, 1, 0.8));
		S_M_G->insert(new EDGE(3, 2, 0.55));
		S_M_G->insert(new EDGE(3, 0, 0.8));
		S_M_G->insert(new EDGE(3, 4, 0.7));
		S_M_G->insert(new EDGE(4, 2, 0.7));
		S_M_G->insert(new EDGE(2, 3, 0.9));
		S_M_G->insert(new EDGE(0, 4, 0.9));
		S_M_G->insert(new EDGE(2, 4, 0.95));
		S_M_G->insert(new EDGE(1, 4, 0.3));
		S_M_G->insert(new EDGE(1, 5, 0.3));
		cout << "\nМетод Дейкстры (для неориентированного графа):" << endl;
		cout << "\nИсток - 0, сток - 3" << endl;
		t1 = clock();
		block3("SparseMultiGRAPH", 0, 3);
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nПостроение остовного дерева:" << endl;
		t1 = clock();
		block5("SparseMultiGRAPH");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";

		cout << "\nПостроение минимального остовного дерева методом Краскала:" << endl;
		t1 = clock();
		block6("SparseMultiGRAPH");
		cout << "\nВремя выполнения: " << clock() - t1 << endl;

		cout << "\n---------------------------------------------------\n";
	}
};

void main(void)
{
	Interaction();
}