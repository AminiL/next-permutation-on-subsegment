#include <iostream>
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <cmath>
#include <ctime>
#include <functional>
#include <istream>
#include <ostream>
#include <random>
namespace next_permutation_on_subsegment {
	enum type { SUM = 1, INSERT, ERASE, ASSIGN, PLUS, NEXT_PERMUTATION, PREV_PERMUTATION };
	struct Query {
		long long type;
		long long value;
		size_t l, r, pos;
		Query() {}
	};
	Query get_query(std::istream &in = std::cin) {
		Query q;
		in >> q.type;

		if (q.type == ERASE)
			in >> q.pos;

		else if (q.type == ASSIGN || q.type == PLUS)
			in >> q.value >> q.l >> q.r;

		else if (q.type == INSERT)
			in >> q.value >> q.pos;
		else
			in >> q.l >> q.r;
		return q;
	}
	class Query_in {
	private:
		long long cnt_;
		std::vector < Query > queries_;
		std::vector < long long > elements_;

	public:
		explicit Query_in(const std::vector < long long > &elements, const std::vector < Query > &queries = {}) :
			elements_(elements),
			cnt_(queries.size()),
			queries_(queries)
		{}

		void add(Query q) {
			queries_.push_back(q);
		}

		Query get_query_from_pos(size_t pos) const {
			return queries_[pos];
		}

		void change_on_pos(size_t pos, Query &q) {
			queries_[pos] = q;
		}

		long long get_cnt() const {
			return cnt_;
		}
		std::vector < long long > get_vec_for_tree() const {
			return elements_;
		}
	};

	class Query_out {
	private:
		std::vector < long long > out_;
		std::vector < long long > arr_;
	public:
		explicit Query_out(const std::vector < long long > &out, const std::vector < long long > &arr) :
			out_(out),
			arr_(arr)
		{}

		Query_out() {}
		static void output_vec(const std::vector < long long > &vec, const char delimiter, std::ostream& out) {
			for (long long x : vec) {
				out << x << delimiter;
			}
		}
		void output(std::ostream& out) const {
			output_vec(out_, '\n', out);
			output_vec(arr_, ' ', out);
			out << '\n';
		}
		void add_ans(long long ans) {
			out_.push_back(ans);
		}

		std::vector < long long > get_vec() {
			return out_;
		}

	};

	long long get_rand() {
		std::random_device rd;
		std::mt19937 gen(rd());
		//std::cout << "gen: " << gen() << '\n';
		return gen();
	}

	class Node {
	private:
		static const long long inf = std::numeric_limits < long long >::max();
		Node *left_child_, *right_child_, *parent_;
		long long priority_;
		long long value_;
		size_t size_; //size of subtree
		long long min_;
		long long max_;
		long long sum_;
		bool reversed_;
		bool non_decreasing_;
		bool non_increasing_;
		enum upd_value_on_subsegment { ASSIGN_ON_SUBSEGMENT = 1, PLUS_ON_SUBSEGMENT = 0 };
		enum upd_permutation_on_subseegment { NEXT_PERMUTATION_ON_SUBSEGMENT = 1, PREVIOUS_PERMUTATION_ON_SUBSEGMENT = 0 };
		struct change {
			static const int time_for_no_update = -1;
			static const int value_for_no_update = 0;
			long long value;
			long long time_of_query;
			change(long long value, long long time_of_query) :
				value(value),
				time_of_query(time_of_query)
			{}
			bool smth_to_upd() {
				return time_of_query != time_for_no_update;
			}
		};

		change to_assign_;
		change to_plus_;

		inline void push_for_child_for_plus(Node* child) {
			if (child) {
				change *tmp = &child->to_plus_;
				if (child->to_assign_.smth_to_upd()) {
					tmp = (&child->to_assign_);
				}
				tmp->value += to_plus_.value;
				tmp->time_of_query = to_plus_.time_of_query;
			}
		}

		inline void push_only_for_plus() {
			if (to_plus_.smth_to_upd()) {
				push_for_child_for_plus(left_child_);
				push_for_child_for_plus(right_child_);
				sum_ += to_plus_.value * size_;
				max_ += to_plus_.value;
				min_ += to_plus_.value;
				value_ += to_plus_.value;
				to_plus_ = change(change::value_for_no_update, change::time_for_no_update);
			}
		}

		inline void push_for_reversed() {
			reversed_ = 0;
			std::swap(non_increasing_, non_decreasing_);
			if (left_child_)
				left_child_->reversed_ ^= 1;
			if (right_child_)
				right_child_->reversed_ ^= 1;
			std::swap(left_child_, right_child_);
		}

		inline void push_for_assign() {
			non_increasing_ = non_decreasing_ = 0;
			if (to_assign_.time_of_query > to_plus_.time_of_query) {
				to_plus_ = change(change::value_for_no_update, change::time_for_no_update);
			}
			else {
				to_assign_.time_of_query = to_plus_.time_of_query;
				to_assign_.value += to_plus_.value;
				to_plus_ = change(change::value_for_no_update, change::time_for_no_update);
			}
			sum_ = to_assign_.value * size_;
			value_ = max_ = min_ = to_assign_.value;
			if (left_child_) {
				left_child_->to_assign_ = to_assign_;
			}
			if (right_child_)
				right_child_->to_assign_ = to_assign_;
			to_assign_ = change(change::value_for_no_update, change::time_for_no_update);
		}

		void push() {
			if (reversed_) {
				push_for_reversed();
			}
			if (to_assign_.smth_to_upd()) {
				push_for_assign();
			}
			else {
				push_only_for_plus();
			}
		}
		template < typename Comparator >
		bool value_of_monotone(bool in_childs, long long value_left, long long value_right, Comparator comp) {
			return in_childs | comp(value_left, value_) | comp(value_, value_right);
		}
		void relax() {
			if (left_child_)
				left_child_->push();
			if (right_child_)
				right_child_->push();
			size_ = size(left_child_) + size(right_child_) + 1;
			sum_ = sum(left_child_) + sum(right_child_) + value_;

			max_ = std::max(max_on_subtree(left_child_), std::max(max_on_subtree(right_child_), value_));
			min_ = std::min(min_on_subtree(left_child_), std::min(min_on_subtree(right_child_), value_));
			non_decreasing_ = value_of_monotone(non_decreasing(left_child_) | non_decreasing(right_child_), min_on_subtree(left_child_), max_on_subtree(right_child_), std::less < long long >());
			non_increasing_ = value_of_monotone(non_increasing(left_child_) | non_increasing(right_child_), max_on_subtree(left_child_), min_on_subtree(right_child_), std::greater < long long >());
		}

		static long long find_sum(Node *v) {
			long long ret = sum(v);
			return ret;
		}

		static	long long push_q(Node *v, long long x, bool is_assign) {
			static int query_time = 0;
			query_time++;
			if (v)
				v->push();
			if (is_assign)
				v->to_assign_ = change(x, query_time);
			else
				v->to_plus_ = change(x, query_time);
			return 0;
		}

		static Node *suf_for_permutation(Node *v, bool need_decrease_suf) {
			long long passed_min_or_max = (need_decrease_suf ? -inf : inf);
			if (!v)
				return nullptr;
			if (!(need_decrease_suf ? non_decreasing(v) : non_increasing(v))) {
				return nullptr;
			}
			while (true) {
				if (v)
					v->push();
				if ((need_decrease_suf ? non_decreasing(v->right_child_) : non_increasing(v->right_child_))) {
					v = v->right_child_;
					continue;
				}
				if (need_decrease_suf ? min_on_subtree(v->right_child_) < passed_min_or_max : max_on_subtree(v->right_child_) > passed_min_or_max) {
					v = v->right_child_;
					continue;
				}
				passed_min_or_max = (need_decrease_suf ? std::max(passed_min_or_max, max_on_subtree(v->right_child_)) : std::min(min_on_subtree(v->right_child_), passed_min_or_max));
				if (need_decrease_suf ? v->value_ < passed_min_or_max : v->value_ > passed_min_or_max)
					return v;
				passed_min_or_max = (need_decrease_suf ? std::max(passed_min_or_max, v->value_) : std::min(v->value_, passed_min_or_max));
				v = v->left_child_;
			}
		}

		static Node *first_smaller_or_bigger(Node *v, long long value, bool is_bigger) {
			if (!v)
				return nullptr;
			v->push();
			Node *ret = nullptr;
			if (!is_bigger ? v->value_ < value : v->value_ > value) {
				ret = v;
				Node *tmp = first_smaller_or_bigger(!is_bigger ? v->right_child_ : v->left_child_, value, is_bigger);
				if (tmp)
					ret = tmp;
				return ret;
			}
			return first_smaller_or_bigger(!is_bigger ? v->left_child_ : v->right_child_, value, is_bigger);
		}

		static long long permutation(Node *v, bool is_next_permutation) {
			Node *suf = suf_for_permutation(v, is_next_permutation);
			if (!suf) {
				v->reversed_ ^= 1;
				return 0;
			}
			long long pos_suf = find_pos_by_node(suf);
			auto tmp_v = split(v, pos_suf);
			auto tmp_suf = split(tmp_v.second, 1);
			if (is_next_permutation)
				tmp_suf.second->reversed_ ^= 1;
			Node *up = nullptr;
			up = first_smaller_or_bigger(tmp_suf.second, tmp_suf.first->value_, is_next_permutation);
			long long pos_up = find_pos_by_node(up);
			auto tmp_up = split(tmp_suf.second, pos_up);
			auto tmp_real_up = split(tmp_up.second, 1);
			std::swap(tmp_suf.first, tmp_real_up.first);
			up = merge(tmp_up.first, merge(tmp_real_up.first, tmp_real_up.second));
			if (!is_next_permutation)
				up->reversed_ ^= 1;
			v = merge(tmp_v.first, merge(tmp_suf.first, up));
			return 0;
		}

		static long long make_operation_on_subsegment(Node *root, size_t l, size_t r, std::function<long long(Node*)>func) {
			auto tmp = split(root, r + 1);
			auto tmp2 = split(tmp.first, l);
			long long ret = func(tmp2.second);
			merge(merge(tmp2.first, tmp2.second), tmp.second);
			return ret;
		}

		static void assign_or_plus_on_subsegment(Node *root, long long value, size_t l, size_t r, bool is_assign) {
			make_operation_on_subsegment(root, l, r, [value, is_assign](Node *v) -> long long {
				return push_q(v, value, is_assign);
			});
		}

		static void make_permutation_on_subsegment(Node *root, size_t l, size_t r, bool is_next_permutation) {
			make_operation_on_subsegment(root, l, r, [is_next_permutation](Node *v) -> long long {
				return permutation(v, is_next_permutation);
			});
		}

	public:
		explicit Node(long long x) :
			value_(x),
			size_(1),
			priority_(get_rand()),
			sum_(x),
			min_(x),
			max_(x),
			left_child_(nullptr),
			right_child_(nullptr),
			parent_(nullptr),
			reversed_(0),
			to_assign_(change(0, -1)),
			to_plus_(change(0, -1)),
			non_decreasing_(0),
			non_increasing_(0)
		{};
		static void delete_Node(Node* v) {
			if (v->left_child_)
				delete_Node(v->left_child_);
			if (v->right_child_)
				delete_Node(v->right_child_);
			delete v;
			//delete this;
		}
		static long long sum(Node *v) {
			if (!v)
				return 0;
			v->push();
			return v->sum_;
		}

		static long long min_on_subtree(Node *v) {
			if (!v)
				return inf;
			v->push();
			return v->min_;
		}

		static long long max_on_subtree(Node *v) {
			if (!v)
				return -inf;
			v->push();
			return v->max_;
		}

		static size_t size(Node *v) {
			if (!v)
				return 0;
			v->push();
			return v->size_;
		}

		static bool non_decreasing(Node* v) {
			if (!v)
				return 0;
			v->push();
			return v->non_decreasing_;
		}

		static bool non_increasing(Node* v) {
			if (!v)
				return 0;
			v->push();
			return v->non_increasing_;
		}

		static Node *merge(Node *l, Node *r) {
			if (l)
				l->push();
			if (r)
				r->push();
			if (!l) {
				return r;
			}
			if (!r)
				return l;
			if (l->priority_ < r->priority_) {
				l->right_child_ = merge(l->right_child_, r);
				if (l->right_child_)
					l->right_child_->parent_ = l;
				l->relax();
				return l;
			}
			r->left_child_ = merge(l, r->left_child_);
			if (r->left_child_)
				r->left_child_->parent_ = r;
			r->relax();
			return r;
		}

		static std::pair < Node *, Node * > split(Node *v, size_t size_of_left_part) {
			if (!v)
				return std::make_pair(nullptr, nullptr);
			v->parent_ = nullptr;
			v->push();
			if (size(v->left_child_) >= size_of_left_part) {
				auto tmp = split(v->left_child_, size_of_left_part);
				v->left_child_ = tmp.second;
				if (v->left_child_)
					v->left_child_->parent_ = v;
				v->relax();
				return std::make_pair(tmp.first, v);
			}
			auto tmp = split(v->right_child_, size_of_left_part - size(v->left_child_) - 1);
			v->right_child_ = tmp.first;
			if (v->right_child_)
				v->right_child_->parent_ = v;
			v->relax();
			return std::make_pair(v, tmp.second);
		}

		static size_t find_pos_by_node(Node *v) {
			long long ret = 0;
			if (v->reversed_) {
				ret += size(v->right_child_);
			}
			else
				ret = size(v->left_child_);

			Node *prev = v;
			v = v->parent_;
			while (v != nullptr) {
				if (v->reversed_) {
					if (v->left_child_ == prev)
						ret = size(v->left_child_) - ret + size(v->right_child_);
					else
						ret = size(v->right_child_) - ret - 1;
				}
				else {
					if (v->right_child_ == prev)
						ret += size(v->left_child_) + 1;
				}
				prev = v;
				v = v->parent_;
			}
			return ret;
		}

		static Node* erase(Node *root, size_t pos) {
			auto tmp = split(root, pos);
			auto tmp2 = split(tmp.second, 1);
			delete tmp2.first;
			root = merge(tmp.first, tmp2.second);
			return root;
		}

		static Node *insert(Node *root, size_t pos, long long value) {
			auto tmp = split(root, pos);
			root = merge(merge(tmp.first, new Node(value)), tmp.second);
			return root;
		}

		static long long sum_on_subsegment(Node *root, size_t l, size_t r) {
			return make_operation_on_subsegment(root, l, r, [](Node *v) -> long long {
				return find_sum(v);
			});
		}

		static void assign_on_subsegment(Node *root, long long value, size_t l, size_t r) {
			assign_or_plus_on_subsegment(root, value, l, r, ASSIGN_ON_SUBSEGMENT);
		}

		static void plus_on_subsegment(Node *root, long long value, size_t l, size_t r) {
			assign_or_plus_on_subsegment(root, value, l, r, PLUS_ON_SUBSEGMENT);
		}

		static void next_permutation_on_subsegment(Node *root, size_t l, size_t r) {
			make_permutation_on_subsegment(root, l, r, NEXT_PERMUTATION_ON_SUBSEGMENT);
		}

		static void previous_permutation_on_subsegment(Node* root, size_t l, size_t r) {
			make_permutation_on_subsegment(root, l, r, PREVIOUS_PERMUTATION_ON_SUBSEGMENT);
		}

		static void output(Node *v, std::ostream &out = std::cerr) {
			if (!v)
				return;
			v->push();
			output(v->left_child_, out);
			out << v->value_ << " ";
			output(v->right_child_, out);
		}
		static void to_vec(Node *v, std::vector < long long > &vec) {
			if (!v) {
				return;
			}
			v->push();
			to_vec(v->left_child_, vec);
			vec.push_back(v->value_);
			to_vec(v->right_child_, vec);
		}
	};
	class Treap {
	private:
		Node* root_;
		Query_out answers_;

	public:
		explicit Treap(const std::vector < long long > &arr) {
			root_ = nullptr;
			for (int x : arr)
				root_ = Node::merge(root_, new Node(x));
		}
		~Treap() {
			Node::delete_Node(root_);
		}
		long long sum_on_subsegment(size_t l, size_t r) {
			return Node::sum_on_subsegment(root_, l, r);
		}

		void insert(long long x, size_t pos) {
			root_ = Node::insert(root_, pos, x);
		}

		void erase(size_t pos) {
			root_ = Node::erase(root_, pos);
		}

		void assign_on_subsegment(long long x, size_t l, size_t r) {
			Node::assign_on_subsegment(root_, x, l, r);
		}

		void plus_on_subsegment(long long x, size_t l, size_t r) {
			Node::plus_on_subsegment(root_, x, l, r);
		}

		void next_permutation_on_subsegment(size_t l, size_t r) {
			Node::next_permutation_on_subsegment(root_, l, r);
		}

		void previous_permutation_on_subsegment(size_t l, size_t r) {
			Node::previous_permutation_on_subsegment(root_, l, r);
		}

		void output(std::ostream &out = std::cerr) {
			Node::output(root_, out);
		}
		std::vector < long long > to_vec() {
			std::vector < long long > ret;
			Node::to_vec(root_, ret);
			return ret;
		}

	};

	std::vector < long long > read_vec_numbers(int cnt, std::istream &in) {
		std::vector < long long > vec;
		for (int i = 0; i < cnt; ++i) {
			long long x;
			in >> x;
			vec.push_back(x);
		}
		return vec;
	}
	std::vector < long long > read_vec_numbers(std::istream &in) {
		int cnt;
		in >> cnt;
		return read_vec_numbers(cnt, in);
	}

	std::vector < Query > read_vec_query(int cnt, std::istream &in) {
		std::vector < Query > vec;
		while (cnt--) {
			Query q;
			q = get_query(in);
			vec.push_back(q);
		}
		return vec;
	}
	std::vector < Query > read_vec_query(std::istream &in) {
		int cnt;
		in >> cnt;
		return read_vec_query(cnt, in);
	}

	Query_in read(std::istream &in) {
		auto elements = read_vec_numbers(in);
		auto queries = read_vec_query(in);
		return Query_in(elements, queries);
	}
	template < typename T>
	Query_out get_solution(const Query_in& Q) {
		T t(Q.get_vec_for_tree());
		int cnt = Q.get_cnt();
		std::vector < long long > ans;
		for (int i = 0; i < cnt; ++i) {
			Query now = Q.get_query_from_pos(i);
			switch (now.type) {
			case SUM: {
				ans.push_back(t.sum_on_subsegment(now.l, now.r));
				break;
			}
			case INSERT: {
				t.insert(now.value, now.pos);
				break;
			}
			case ERASE: {
				t.erase(now.pos);
				break;
			}
			case ASSIGN: {
				t.assign_on_subsegment(now.value, now.l, now.r);
				break;
			}
			case PLUS: {
				t.plus_on_subsegment(now.value, now.l, now.r);
				break;
			}
			case NEXT_PERMUTATION: {
				t.next_permutation_on_subsegment(now.l, now.r);
				break;
			}
			case PREV_PERMUTATION: {
				t.previous_permutation_on_subsegment(now.l, now.r);
				break;
			}
			}

		}
		return Query_out(ans, t.to_vec());
	}
	void output_ans(Query_out &solution, std::ostream &out) {
		solution.output(out);
	}
}
void solve(std::istream& in = std::cin, std::ostream& out = std::cerr) {
	using namespace next_permutation_on_subsegment;
	Query_in Q_in = read(in);
	Query_out q_out = get_solution < Treap >(Q_in);
	output_ans(q_out, out);
}

int main() {
	std::iostream::sync_with_stdio(false);
	std::cin.tie(NULL);
	//std::cout.tie(NULL);
	solve(std::cin, std::cout);
}
