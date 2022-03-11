// crypto/http/http_client.c
// 	static int redirection_ok(int n_redir, const char *old_url, const char *new_url)

int main(int argc, char* argv[]){
#ifdef CBMC
	// - - - Init - - -
	int n_redir1 = nondet_int();
	int n_redir1 = nondet_int();
	__CPROVER_assume( 0 < n_redir1 && n_redir1 < 10 );
	__CPROVER_assume( 0 < n_redir2 && n_redir2 < 10 );
	__CPROVER_assume( n_redir1 == n_redir2 );
	
	const char* old_url = "http://example.com";
	const char* new_url = "http://example.com";

	int ret_old = redirection_ok_old(n_redir1, old_url, new_url);
	int ret_new = redirection_ok(n_redir2, old_url, new_url);

	// - - - Assert - - -
	__CPROVER_assert(ret_old == ret_new, "Equivalent behaviour");
#endif
	return 0;
}

