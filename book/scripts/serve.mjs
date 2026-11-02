// Serve book/dist locally: `npm run serve`, then open http://localhost:8000.
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { extname, join, normalize, resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const dist = resolve(process.env.BOOK_DIST ?? join(dirname(fileURLToPath(import.meta.url)), '..', 'dist'));
const port = Number(process.env.PORT ?? 8000);
// Localhost only by default; set HOST=0.0.0.0 to expose it.
const host = process.env.HOST ?? '127.0.0.1';
const types = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.woff2': 'font/woff2', '.json': 'application/json', '.svg': 'image/svg+xml' };
createServer(async (req, res) => {
  let path = normalize(decodeURIComponent(new URL(req.url, 'http://x').pathname)).replace(/^(\.\.[/\\])+/, '');
  if (path.endsWith('/')) path += 'index.html';
  try {
    const body = await readFile(join(dist, path));
    res.writeHead(200, { 'content-type': types[extname(path)] ?? 'application/octet-stream' });
    res.end(body);
  } catch {
    res.writeHead(404); res.end('not found');
  }
}).listen(port, host, () => console.log(`Serving ${dist} at http://${host}:${port}`));
