
const express = require("express");
const cors = require("cors");
require("dotenv").config();

const app = express();

// Middleware
app.use(cors());
app.use(express.json());

// Test route
app.get("/", (req, res) => {
    res.send("Welcome to ResQ Emergency Response Backend!");
});

// Backend health check
app.get("/api/health", (req, res) => {
    res.json({
        success: true,
        message: "ResQ backend is running successfully!"
    });
});

// Server port
const PORT = process.env.PORT || 5000;

// Start server
app.listen(PORT, () => {
    console.log(`ResQ server running at http://localhost:${PORT}`);
});
