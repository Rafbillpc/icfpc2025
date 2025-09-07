#include "api.hpp"
#include "httplib.h"
#include <nlohmann/json.hpp>
using namespace nlohmann;

unique_ptr<httplib::SSLClient> client = nullptr;
void make_client(){
  if(!client) {
    client = make_unique<httplib::SSLClient>
      ("31pwr5t6ij.execute-api.eu-west-2.amazonaws.com", 443);
    client->set_connection_timeout(0, 3000000); // 300 milliseconds
    client->set_read_timeout(15, 0); // 5 seconds
    client->set_write_timeout(15, 0); // 5 seconds
  }
}

void check_response(httplib::Result& response) {
  if(!response) {
    cerr << "Unexpected server response:\nNo response from server" << endl;
    exit(1);
  }

  if(response->status != 200 && response->status != 201) {
    cerr << "Unexpected server response:\nHTTP code: " << response->status
         << "\nResponse body: " << response->body << endl;
    exit(2);
  }
}

string get_problem_name(int size, int num_dups) {
  if(num_dups == 1) {
    if(size == 3) return "probatio";
    if(size == 6) return "primus";
    if(size == 12) return "secundus";
    if(size == 18) return "tertius";
    if(size == 24) return "quartus";
    if(size == 30) return "quintus";
  }
  if(num_dups == 2){
    if(size == 6) return "aleph";
    if(size == 12) return "beth";
    if(size == 18) return "gimel";
    if(size == 24) return "daleth";
    if(size == 30) return "he";
  }
  if(num_dups == 3){
    if(size == 6) return "vau";
    if(size == 12) return "zain";
    if(size == 18) return "hhet";
    if(size == 24) return "teth";
    if(size == 30) return "iod";
  }
  impossible();
}

string cached_id;
string get_id() {
  if(cached_id.empty()) {
    ifstream is(".token");
    getline(is, cached_id);
  }
  return cached_id;
}

void api_select(string const& problem) {
  make_client();

  string url = "/select";

  json j;
  j["id"] = get_id();
  j["problemName"] = problem;
  auto str = j.dump();

  auto response = client->Post(url.c_str(), str.c_str(), "application/json");
  check_response(response);
}

vector<vector<int>> api_explore(vector<string> const& data) {
  make_client();

  string url = "/explore";

  json j;
  j["id"] = get_id();
  for(string s : data) j["plans"].emplace_back(s);
  auto str = j.dump();

  auto response = client->Post(url.c_str(), str.c_str(), "application/json");
  check_response(response);
  istringstream is(response->body);
  json r; is >> r;
  vector<vector<int>> x;
  for(json const& w : r["results"]) {
    x.eb();
    for(json const& v : w) x.back().eb(v.get<int>());
  }
  return x;
}

bool api_guess(layout const& L) {
  make_client();

  string url = "/guess";

  json j;
  j["id"] = get_id();
  FOR(i, L.size*L.num_dups) j["map"]["rooms"].emplace_back(L.tag[i]);
  j["map"]["startingRoom"] = L.start;
  auto doors = L.get_doors();
  // debug(doors);
  for(auto [a,b,c,d] : doors) {
    json v;
    v["from"]["room"] = a;
    v["from"]["door"] = b;
    v["to"]["room"] = c;
    v["to"]["door"] = d;
    j["map"]["connections"].emplace_back(v);
  }
  
  auto str = j.dump();

  // debug(str);

  auto response = client->Post(url.c_str(), str.c_str(), "application/json");
  if(!response || (response->status != 200 && response->status != 201)) {
    // TODO: handle
    return false;
  }
  // check_response(response);
  debug(response->body);
  istringstream is(response->body);
  json r; is >> r;
  return r["correct"].get<bool>();
}
