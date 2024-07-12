namespace CaDiCaL {

int64_t Solver::propagations() const {
  TRACE("propagations");
  REQUIRE_VALID_STATE();
  int64_t res = internal->stats.propagations.search;
  LOG_API_CALL_RETURNS("propagations", res);
  return res;
}

int64_t Solver::decisions() const {
  TRACE("decisions");
  REQUIRE_VALID_STATE();
  int64_t res = internal->stats.decisions;
  LOG_API_CALL_RETURNS("decisions", res);
  return res;
}

int64_t Solver::conflicts() const {
  TRACE("conflicts");
  REQUIRE_VALID_STATE();
  int64_t res = internal->stats.conflicts;
  LOG_API_CALL_RETURNS("conflicts", res);
  return res;
}

} // namespace CaDiCaL
